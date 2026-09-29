-- Prove2me | solution 1 for finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ebd526f8-a13c-586b-a216-b2597d7e0f2d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range

set_option autoImplicit false

open scoped TensorProduct

namespace A1v

section Basic
variable (O : Type*) [Ring O]

theorem includeRight_injective [Module.Free ℤ O] :
    Function.Injective (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) := by
  have h1 : Function.Injective ((Algebra.linearMap ℤ ℚ).rTensor O) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (fun x y hxy => by
      have : ((x : ℤ) : ℚ) = ((y : ℤ) : ℚ) := hxy
      exact_mod_cast this)
  have h2 : Function.Injective (TensorProduct.lid ℤ O).symm := (TensorProduct.lid ℤ O).symm.injective
  have heq : ∀ o : O, (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) o =
      ((Algebra.linearMap ℤ ℚ).rTensor O) ((TensorProduct.lid ℤ O).symm o) := fun o => by
    simp [Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul]
  intro x y hxy
  rw [heq, heq] at hxy
  exact h2 (h1 hxy)

theorem exists_nsmul_eq_one_tmul (x : ℚ ⊗[ℤ] O) : ∃ n : ℕ, n ≠ 0 ∧ ∃ o : O, (n : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] o := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q o =>
    refine ⟨q.den, q.den_nz, q.num • o, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, Rat.den_mul_eq_num, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Int.smul_one_eq_cast]
  | add x y hx hy =>
    obtain ⟨m, hm, u, hu⟩ := hx
    obtain ⟨n, hn, w, hw⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, (n : ℤ) • u + (m : ℤ) • w, ?_⟩
    rw [smul_add, Nat.cast_mul, mul_comm (m : ℚ), mul_smul, hu, mul_comm (n : ℚ), mul_smul, hw,
      TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul', Int.smul_one_eq_cast, Int.smul_one_eq_cast,
      Int.cast_natCast, Int.cast_natCast, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

theorem nontrivial [Module.Free ℤ O] [Nontrivial O] : Nontrivial (ℚ ⊗[ℤ] O) := by
  refine ⟨⟨(Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) 1, (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) 0, ?_⟩⟩
  exact fun h => one_ne_zero (includeRight_injective O h)

theorem noZeroDivisors [Module.Free ℤ O] [NoZeroDivisors O] : NoZeroDivisors (ℚ ⊗[ℤ] O) := by
  refine ⟨fun {x y} hxy => ?_⟩
  obtain ⟨m, hm, u, hu⟩ := exists_nsmul_eq_one_tmul O x
  obtain ⟨n, hn, w, hw⟩ := exists_nsmul_eq_one_tmul O y
  have h : ((m : ℚ) • x) * ((n : ℚ) • y) = (1 : ℚ) ⊗ₜ[ℤ] (u * w) := by
    rw [hu, hw, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [smul_mul_smul_comm, hxy, smul_zero] at h
  have huw : u * w = 0 := by
    apply includeRight_injective O
    rw [map_zero, Algebra.TensorProduct.includeRight_apply, ← h]
  rcases mul_eq_zero.mp huw with h0 | h0
  · left
    have : (m : ℚ) • x = 0 := by rw [hu, h0, TensorProduct.tmul_zero]
    exact (smul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr hm)
  · right
    have : (n : ℚ) • y = 0 := by rw [hw, h0, TensorProduct.tmul_zero]
    exact (smul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr hn)

theorem finrank_eq_and_isUnit [IsDomain O] [Module.Free ℤ O] [Module.Finite ℤ O] (hrank : Module.finrank ℤ O = 4) :
    Module.finrank ℚ (ℚ ⊗[ℤ] O) = 4 ∧ ∀ x : ℚ ⊗[ℤ] O, x ≠ 0 → IsUnit x := by
  haveI := nontrivial O
  haveI := noZeroDivisors O
  haveI : IsDomain (ℚ ⊗[ℤ] O) := NoZeroDivisors.to_isDomain _
  refine ⟨by rw [Module.finrank_baseChange, hrank], ?_⟩
  letI := divisionRingOfFiniteDimensional ℚ (ℚ ⊗[ℤ] O)
  exact fun x hx => isUnit_iff_ne_zero.mpr hx

theorem center_subset_range [IsDomain O] [Module.Free ℤ O] [Module.Finite ℤ O] (hrank : Module.finrank ℤ O = 4)
    (hnc : ∃ u w : O, u * w ≠ w * u) :
    ∀ z : ℚ ⊗[ℤ] O, (∀ x : ℚ ⊗[ℤ] O, z * x = x * z) → z ∈ Set.range (algebraMap ℚ (ℚ ⊗[ℤ] O)) := by
  classical
  haveI := nontrivial O
  haveI := noZeroDivisors O
  haveI : IsDomain (ℚ ⊗[ℤ] O) := NoZeroDivisors.to_isDomain _
  have hdim : Module.finrank ℚ (ℚ ⊗[ℤ] O) = 4 := by rw [Module.finrank_baseChange, hrank]
  letI instD : DivisionRing (ℚ ⊗[ℤ] O) := divisionRingOfFiniteDimensional ℚ (ℚ ⊗[ℤ] O)

  have hnc' : ∃ x y : ℚ ⊗[ℤ] O, x * y ≠ y * x := by
    obtain ⟨u, w, huw⟩ := hnc
    refine ⟨(Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) u, (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) w, fun h => huw ?_⟩
    apply includeRight_injective O
    rw [map_mul, map_mul, h]

  set Z : Subalgebra ℚ (ℚ ⊗[ℤ] O) := Subalgebra.center ℚ (ℚ ⊗[ℤ] O) with hZ
  have hZf : IsField ↥Z := by
    refine ⟨⟨0, 1, zero_ne_one⟩, fun x y => mul_comm x y, fun {x} hx => ?_⟩
    have hx0 : (x : ℚ ⊗[ℤ] O) ≠ 0 := fun h => hx (Subtype.ext h)
    have hxinv : (x : ℚ ⊗[ℤ] O)⁻¹ ∈ Z := by
      refine Subalgebra.mem_center_iff.mpr fun y => ?_
      have hc : (x : ℚ ⊗[ℤ] O) * y = y * x := (Subalgebra.mem_center_iff.mp x.2 y).symm
      calc y * (x : ℚ ⊗[ℤ] O)⁻¹ = (x : ℚ ⊗[ℤ] O)⁻¹ * ((x : ℚ ⊗[ℤ] O) * y) * (x : ℚ ⊗[ℤ] O)⁻¹ := by
            rw [← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
        _ = (x : ℚ ⊗[ℤ] O)⁻¹ * y := by rw [hc]; simp only [mul_assoc, mul_inv_cancel₀ hx0, mul_one]
    exact ⟨⟨_, hxinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
  letI instZ : Field ↥Z := hZf.toField

  haveI : Module.Finite ↥Z (ℚ ⊗[ℤ] O) := Module.Finite.of_restrictScalars_finite ℚ ↥Z (ℚ ⊗[ℤ] O)
  have htower : Module.finrank ℚ ↥Z * Module.finrank ↥Z (ℚ ⊗[ℤ] O) = 4 := by
    rw [Module.finrank_mul_finrank, hdim]

  have hspan : ∀ (x y : ℚ ⊗[ℤ] O), Module.finrank ↥Z (ℚ ⊗[ℤ] O) ≤ 2 → x * y = y * x := by
    intro x y h2
    by_cases hxZ : x ∈ Z
    · exact Subalgebra.mem_center_iff.mp hxZ y |>.symm
    ·
      have hli : LinearIndependent ↥Z ![(1 : ℚ ⊗[ℤ] O), x] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        by_cases ht : t = 0
        · simp only [ht, zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
          exact ⟨hst, ht⟩
        · exfalso; apply hxZ
          have key : x = -((t⁻¹ * s : ↥Z) • (1 : ℚ ⊗[ℤ] O)) := by
            have := congrArg (fun v => (t⁻¹ : ↥Z) • v) hst
            simp only [smul_add, smul_smul, inv_mul_cancel₀ ht, one_smul, smul_zero] at this
            exact eq_neg_of_add_eq_zero_right this
          have hsm : ((t⁻¹ * s : ↥Z) • (1 : ℚ ⊗[ℤ] O)) = ((t⁻¹ * s : ↥Z) : ℚ ⊗[ℤ] O) := by
            change ((t⁻¹ * s : ↥Z) : ℚ ⊗[ℤ] O) * 1 = _
            rw [mul_one]
          rw [key, hsm]
          exact Z.neg_mem (SetLike.coe_mem _)
      have hcard : Fintype.card (Fin 2) = Module.finrank ↥Z (ℚ ⊗[ℤ] O) :=
        le_antisymm (by simpa using hli.fintype_card_le_finrank) (by simpa using h2)
      let bs := basisOfLinearIndependentOfCardEqFinrank hli hcard
      obtain ⟨c, hc⟩ : ∃ c : Fin 2 → ↥Z, y = ∑ i, c i • ![(1 : ℚ ⊗[ℤ] O), x] i :=
        ⟨fun i => bs.repr y i, by
          conv_lhs => rw [← bs.sum_repr y]
          simp only [bs, coe_basisOfLinearIndependentOfCardEqFinrank]⟩
      rw [hc]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      have h0 : ∀ c : ↥Z, c • (1 : ℚ ⊗[ℤ] O) = (c : ℚ ⊗[ℤ] O) := fun c => by
        change (c : ℚ ⊗[ℤ] O) * 1 = _; rw [mul_one]
      have h1 : ∀ c : ↥Z, c • x = (c : ℚ ⊗[ℤ] O) * x := fun c => rfl
      rw [h0, h1]
      have hc0 := Subalgebra.mem_center_iff.mp (c 0).2
      have hc1 := Subalgebra.mem_center_iff.mp (c 1).2
      rw [mul_add, add_mul, hc0 x, ← mul_assoc, hc1 x, mul_assoc]
  have hZ1 : Module.finrank ℚ ↥Z = 1 := by
    obtain ⟨x, y, hxy⟩ := hnc'
    have h3 : 3 ≤ Module.finrank ↥Z (ℚ ⊗[ℤ] O) := by
      by_contra h; exact hxy (hspan x y (by omega))
    have hZpos : 0 < Module.finrank ℚ ↥Z := Module.finrank_pos
    have ha4 : Module.finrank ℚ ↥Z ≤ 4 := Nat.le_of_dvd (by norm_num) (Dvd.intro _ htower)
    generalize ha : Module.finrank ℚ ↥Z = A at htower hZpos ha4
    generalize hb : Module.finrank ↥Z (ℚ ⊗[ℤ] O) = B at htower h3
    interval_cases A <;> omega

  intro z hz
  have hzZ : z ∈ Z := by rw [hZ, Subalgebra.mem_center_iff]; exact fun y => (hz y).symm
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨1, Z.one_mem⟩ : ↥Z) (by
      intro h; exact one_ne_zero (congrArg Subtype.val h))).mp hZ1 ⟨z, hzZ⟩
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simp only [SetLike.val_smul] at this
  rw [← this, Algebra.algebraMap_eq_smul_one]
end Basic

end A1v

open scoped Quaternion
open IsDedekindDomain NumberField

open A1v in
theorem solution
    (O : Type*) [Ring O] [IsDomain O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hrank : Module.finrank ℤ O = 4)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ])) :
    Module.finrank ℚ (ℚ ⊗[ℤ] O) = 4 ∧
      (∀ x : ℚ ⊗[ℤ] O, x ≠ 0 → IsUnit x) ∧
      (∀ z : ℚ ⊗[ℤ] O, (∀ x : ℚ ⊗[ℤ] O, z * x = x * z) →
        z ∈ Set.range (algebraMap ℚ (ℚ ⊗[ℤ] O))) := by
  classical

  have hnc : ∃ u w : O, u * w ≠ w * u := by
    by_contra hall
    push Not at hall
    obtain ⟨φ⟩ := hℓ
    have hcomm : ∀ s t : ℤ_[ℓ] ⊗[ℤ] O, s * t = t * s := by
      intro s t
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul c u =>
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul d w => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm c d, hall u w]
        | add x y hx hy => rw [mul_add, add_mul, hx, hy]
      | add x y hx hy => rw [add_mul, mul_add, hx, hy]
    have hM : ∀ A B : Matrix (Fin 2) (Fin 2) ℤ_[ℓ], A * B = B * A := fun A B => by
      have := hcomm (φ.symm A) (φ.symm B)
      simpa using congrArg φ this
    have h := hM !![0, 1; 0, 0] !![0, 0; 1, 0]
    simp only [Matrix.mul_fin_two] at h
    have h00 := congrFun (congrFun h 0) 0
    simp at h00
  obtain ⟨h1, h2⟩ := finrank_eq_and_isUnit O hrank
  exact ⟨h1, h2, center_subset_range O hrank hnc⟩

end S_finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range
end P2MW
export P2MW.S_finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range (solution)
