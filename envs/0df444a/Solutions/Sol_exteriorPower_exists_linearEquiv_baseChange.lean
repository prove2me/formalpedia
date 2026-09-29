-- Prove2me | solution 1 for exteriorPower.exists_linearEquiv_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b107cf2d-9c0f-5106-be83-668ef050932a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exteriorPower_exists_linearEquiv_baseChange

open scoped TensorProduct

namespace ExteriorPowerBaseChange

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ)

noncomputable scoped instance instModuleR : Module R (⋀[A]^n (A ⊗[R] M)) := Module.compHom _ (algebraMap R A)

scoped instance instIsScalarTowerR : IsScalarTower R A (⋀[A]^n (A ⊗[R] M)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def ιMultiBC : M [⋀^Fin n]→ₗ[R] (⋀[A]^n (A ⊗[R] M)) :=
  { ((exteriorPower.ιMulti A n (M := A ⊗[R] M)).toMultilinearMap.restrictScalars R).compLinearMap
      (fun _ => TensorProduct.mk R A M 1) with
    map_eq_zero_of_eq' := fun v i j h hij =>
      (exteriorPower.ιMulti A n (M := A ⊗[R] M)).map_eq_zero_of_eq (fun k => (1 : A) ⊗ₜ[R] v k)
        (by simp [h]) hij }

@[scoped simp] lemma ιMultiBC_apply (m : Fin n → M) :
    ιMultiBC R A M n m = exteriorPower.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i) := rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def toBC : A ⊗[R] (⋀[R]^n M) →ₗ[A] (⋀[A]^n (A ⊗[R] M)) :=
  LinearMap.liftBaseChange A (exteriorPower.alternatingMapLinearEquiv (ιMultiBC R A M n))

lemma toBC_tmul_ιMulti (a : A) (m : Fin n → M) :
    toBC R A M n (a ⊗ₜ exteriorPower.ιMulti R n m) =
      a • exteriorPower.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i) := by
  simp [toBC, LinearMap.liftBaseChange_tmul]

noncomputable def fBC : A ⊗[R] M →ₗ[A] A ⊗[R] ExteriorAlgebra R M :=
  (ExteriorAlgebra.ι R (M := M)).baseChange A

lemma fBC_tmul (a : A) (m : M) : fBC R A M (a ⊗ₜ m) = a ⊗ₜ ExteriorAlgebra.ι R m := rfl

lemma fBC_mul_fBC_add_swap (x y : A ⊗[R] M) :
    fBC R A M x * fBC R A M y + fBC R A M y * fBC R A M x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b m' =>
      simp only [fBC_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [mul_comm b a, ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap, TensorProduct.tmul_zero]
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, mul_add, add_mul]

      have : fBC R A M (a ⊗ₜ[R] m) * fBC R A M y₁ + fBC R A M (a ⊗ₜ[R] m) * fBC R A M y₂ +
          (fBC R A M y₁ * fBC R A M (a ⊗ₜ[R] m) + fBC R A M y₂ * fBC R A M (a ⊗ₜ[R] m)) =
          (fBC R A M (a ⊗ₜ[R] m) * fBC R A M y₁ + fBC R A M y₁ * fBC R A M (a ⊗ₜ[R] m)) +
          (fBC R A M (a ⊗ₜ[R] m) * fBC R A M y₂ + fBC R A M y₂ * fBC R A M (a ⊗ₜ[R] m)) := by abel
      rw [this, h₁, h₂, add_zero]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, mul_add, add_mul]
    have : fBC R A M x₁ * fBC R A M y + fBC R A M x₂ * fBC R A M y +
        (fBC R A M y * fBC R A M x₁ + fBC R A M y * fBC R A M x₂) =
        (fBC R A M x₁ * fBC R A M y + fBC R A M y * fBC R A M x₁) +
        (fBC R A M x₂ * fBC R A M y + fBC R A M y * fBC R A M x₂) := by abel
    rw [this, h₁, h₂, add_zero]

lemma fBC_mul_self (x : A ⊗[R] M) : fBC R A M x * fBC R A M x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [fBC_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
    rw [map_add, add_mul, mul_add, mul_add, hx, hy, zero_add, add_zero, fBC_mul_fBC_add_swap]

noncomputable def Φ : ExteriorAlgebra A (A ⊗[R] M) →ₐ[A] A ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift A ⟨fBC R A M, fBC_mul_self R A M⟩

lemma Φ_ι (x : A ⊗[R] M) : Φ R A M (ExteriorAlgebra.ι A x) = fBC R A M x :=
  ExteriorAlgebra.lift_ι_apply A _ _ x

noncomputable def proj : ExteriorAlgebra R M →ₗ[R] (⋀[R]^n M) :=
  haveI := (ExteriorAlgebra.gradedAlgebra R M).toDecomposition
  (DirectSum.component R ℕ (fun i => ↥(⋀[R]^i M)) n) ∘ₗ
    (DirectSum.decomposeLinearEquiv (fun i : ℕ => ⋀[R]^i M)).toLinearMap

lemma proj_coe (x : ⋀[R]^n M) : proj R M n (x : ExteriorAlgebra R M) = x := by
  letI := (ExteriorAlgebra.gradedAlgebra R M).toDecomposition
  apply Subtype.ext
  simp only [proj, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, ← DirectSum.apply_eq_component]
  exact DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[R]^i M) x.2

noncomputable def ofBC : (⋀[A]^n (A ⊗[R] M)) →ₗ[A] A ⊗[R] (⋀[R]^n M) :=
  ((proj R M n).baseChange A) ∘ₗ (Φ R A M).toLinearMap ∘ₗ (⋀[A]^n (A ⊗[R] M)).subtype

lemma Φ_ιMulti_one_tmul (m : Fin n → M) :
    Φ R A M (ExteriorAlgebra.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i)) =
      (1 : A) ⊗ₜ ExteriorAlgebra.ιMulti R n m := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  have h1 : (List.ofFn (⇑(Φ R A M) ∘ fun i => ExteriorAlgebra.ι A ((1 : A) ⊗ₜ[R] m i))) =
      (List.ofFn fun i => ExteriorAlgebra.ι R (m i)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := ExteriorAlgebra R M)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, Φ_ι, fBC_tmul, Algebra.TensorProduct.includeRight_apply]
  rw [h1, List.prod_hom, Algebra.TensorProduct.includeRight_apply]

lemma ofBC_ιMulti_one_tmul (m : Fin n → M) :
    ofBC R A M n (exteriorPower.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i)) =
      (1 : A) ⊗ₜ exteriorPower.ιMulti R n m := by
  simp only [ofBC, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    exteriorPower.ιMulti_apply_coe, AlgHom.toLinearMap_apply]
  rw [Φ_ιMulti_one_tmul, LinearMap.baseChange_tmul, ← exteriorPower.ιMulti_apply_coe, proj_coe]

lemma ofBC_toBC (x : A ⊗[R] (⋀[R]^n M)) : ofBC R A M n (toBC R A M n x) = x := by
  suffices h : (ofBC R A M n ∘ₗ toBC R A M n) = LinearMap.id from LinearMap.congr_fun h x
  refine TensorProduct.AlgebraTensorModule.ext fun a y => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]

  have key : ∀ y : ⋀[R]^n M, ofBC R A M n (toBC R A M n ((1 : A) ⊗ₜ y)) = (1 : A) ⊗ₜ y := by
    intro y
    have := exteriorPower.linearMap_ext (R := R) (n := n) (M := M)
      (f := ((ofBC R A M n ∘ₗ toBC R A M n).restrictScalars R) ∘ₗ (TensorProduct.mk R A (⋀[R]^n M) 1))
      (g := (TensorProduct.mk R A (⋀[R]^n M) 1)) ?_
    · exact LinearMap.congr_fun this y
    · ext m
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
        TensorProduct.mk_apply, LinearMap.coe_restrictScalars]
      rw [toBC_tmul_ιMulti, one_smul, ofBC_ιMulti_one_tmul]
  have : a ⊗ₜ[R] y = a • ((1 : A) ⊗ₜ[R] y) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, map_smul, key]

lemma span_ιMulti_one_tmul :
    Submodule.span A (Set.range fun m : Fin n → M =>
      exteriorPower.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i)) = ⊤ := by
  have hs : Submodule.span A (Set.range fun m : M => (1 : A) ⊗ₜ[R] m) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul a m =>
      have : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have h := exteriorPower.ιMulti_span_of_span A n (A ⊗[R] M) hs
  rw [eq_top_iff, ← h, Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have hm : ∀ i, ∃ m : M, (1 : A) ⊗ₜ[R] m = a i := fun i => ha ⟨i, rfl⟩
  choose m hm using hm
  refine Submodule.subset_span ⟨m, ?_⟩
  simp only [hm]

lemma toBC_surjective : Function.Surjective (toBC R A M n) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_ιMulti_one_tmul, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  exact ⟨(1 : A) ⊗ₜ exteriorPower.ιMulti R n m, by rw [toBC_tmul_ιMulti, one_smul]⟩

lemma toBC_bijective : Function.Bijective (toBC R A M n) :=
  ⟨fun x y h => by rw [← ofBC_toBC R A M n x, h, ofBC_toBC], toBC_surjective R A M n⟩

end ExteriorPowerBaseChange
p2m_reactivate "P2MW.S_exteriorPower_exists_linearEquiv_baseChange.ExteriorPowerBaseChange"

theorem solution
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    ∃ e : A ⊗[R] (⋀[R]^n M) ≃ₗ[A] ⋀[A]^n (A ⊗[R] M),
      ∀ (a : A) (m : Fin n → M),
        e (a ⊗ₜ exteriorPower.ιMulti R n m) =
          a • exteriorPower.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i) :=
  ⟨LinearEquiv.ofBijective _ (ExteriorPowerBaseChange.toBC_bijective R A M n),
    fun a m => ExteriorPowerBaseChange.toBC_tmul_ιMulti R A M n a m⟩

end S_exteriorPower_exists_linearEquiv_baseChange
end P2MW
export P2MW.S_exteriorPower_exists_linearEquiv_baseChange (solution)
