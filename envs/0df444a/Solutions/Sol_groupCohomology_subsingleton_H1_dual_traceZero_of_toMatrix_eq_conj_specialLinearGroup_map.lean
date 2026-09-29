-- Prove2me | solution 1 for groupCohomology.subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8f51d6c5-03ed-5c0e-8f92-977a58f2c9e7

import Mathlib
import Theorems.Thm_groupCohomology_subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map

set_option autoImplicit false

open groupCohomology Matrix MatrixGroups

namespace P2mCoefSL

section Generic

variable {R G : Type} [CommRing R] [Group G]

lemma exists_eq_sub_of_subsingleton_H1 (A : Rep.{0} R G) [Subsingleton (H1 A)]
    (x : cocycles₁ A) : ∃ m : A, ∀ g : G, x g = A.ρ g m - m := by
  have hx : H1π A x = 0 := Subsingleton.elim _ _
  rw [H1π_eq_zero_iff] at hx
  obtain ⟨m, hm⟩ := hx
  refine ⟨m, fun g => ?_⟩
  have := congrFun hm g
  rw [← this]
  rfl

lemma H1π_eq_zero_of_exists (A : Rep.{0} R G) (x : cocycles₁ A)
    (h : ∃ m : A, ∀ g : G, x g = A.ρ g m - m) : H1π A x = 0 := by
  rw [H1π_eq_zero_iff]
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  funext g
  rw [hm g]
  rfl

lemma subsingleton_H1_of_forall (A : Rep.{0} R G)
    (h : ∀ x : cocycles₁ A, ∃ m : A, ∀ g : G, x g = A.ρ g m - m) : Subsingleton (H1 A) := by
  constructor
  intro a b
  revert b
  refine H1_induction_on a fun x => ?_
  intro b
  refine H1_induction_on b fun y => ?_
  rw [H1π_eq_zero_of_exists A x (h x), H1π_eq_zero_of_exists A y (h y)]

end Generic

section SelfDual

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]

noncomputable abbrev slV (k V : Type) [Field k] [AddCommGroup V] [Module k V] : Submodule k (Module.End k V) :=
  LinearMap.ker (LinearMap.trace k V)

variable {S : Type} [Group S] (σ : S →* Module.End k V)

lemma conj_mem (s : S) (X : Module.End k V) (hX : X ∈ slV k V) : σ s * X * σ s⁻¹ ∈ slV k V := by
  rw [LinearMap.mem_ker] at hX ⊢
  rw [LinearMap.trace_mul_comm k, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul, hX]

noncomputable def ad (s : S) (X : slV k V) : slV k V := ⟨σ s * X * σ s⁻¹, conj_mem σ s X X.2⟩

@[scoped simp] lemma ad_coe (s : S) (X : slV k V) : ((ad σ s X : slV k V) : Module.End k V) = σ s * X * σ s⁻¹ := rfl

lemma ad_add (s : S) (X Y : slV k V) : ad σ s (X + Y) = ad σ s X + ad σ s Y := by
  apply Subtype.ext; simp [mul_add, add_mul]

lemma ad_sub (s : S) (X Y : slV k V) : ad σ s (X - Y) = ad σ s X - ad σ s Y := by
  apply Subtype.ext; simp [mul_sub, sub_mul]

lemma ad_mul (s t : S) (X : slV k V) : ad σ (s * t) X = ad σ s (ad σ t X) := by
  apply Subtype.ext
  simp only [ad_coe, map_mul, _root_.mul_inv_rev]
  simp only [mul_assoc]

lemma ad_one (X : slV k V) : ad σ 1 X = X := by
  apply Subtype.ext; simp

variable [CharP k 3]

noncomputable def Φ [Module (ZMod 3) (slV k V)] : slV k V →ₗ[ZMod 3] Module.Dual (ZMod 3) (slV k V) :=
  letI := ZMod.algebra k 3
  AddMonoidHom.toZModLinearMap 3
    { toFun := fun X => AddMonoidHom.toZModLinearMap 3
        { toFun := fun Y => Algebra.trace (ZMod 3) k (LinearMap.trace k V ((X : Module.End k V) * Y))
          map_zero' := by simp
          map_add' := fun Y Z => by simp [mul_add] }
      map_zero' := by ext Y; simp
      map_add' := fun X Z => by ext Y; simp [add_mul] }

lemma Φ_apply [Module (ZMod 3) (slV k V)] (X Y : slV k V) :
    Φ X Y = (letI := ZMod.algebra k 3; Algebra.trace (ZMod 3) k (LinearMap.trace k V ((X : Module.End k V) * Y))) :=
  rfl

omit [CharP k 3] in
lemma trace_conj_mul (s : S) (X Y : Module.End k V) :
    LinearMap.trace k V (σ s * X * σ s⁻¹ * Y) = LinearMap.trace k V (X * (σ s⁻¹ * Y * σ (s⁻¹)⁻¹)) := by
  rw [inv_inv, mul_assoc (σ s), mul_assoc (σ s), LinearMap.trace_mul_comm k (σ s), ← mul_assoc,
    ← mul_assoc]

lemma Φ_ad [Module (ZMod 3) (slV k V)] (s : S) (X Y : slV k V) :
    Φ (ad σ s X) Y = Φ X (ad σ s⁻¹ Y) := by
  rw [Φ_apply, Φ_apply, ad_coe, ad_coe, trace_conj_mul]

end SelfDual

section Nondeg

variable {k : Type} [Field k] [Finite k] [CharP k 3] {V : Type} [AddCommGroup V] [Module k V]

omit [Finite k] in
lemma three_eq_zero : (3 : k) = 0 := by simpa using CharP.cast_eq_zero k 3

omit [Finite k] in
lemma two_ne_zero' : (2 : k) ≠ 0 := by
  have h3 : (3 : k) = 0 := three_eq_zero
  intro h2
  have : (1 : k) = 0 := by linear_combination h3 - h2
  exact one_ne_zero this

omit [Finite k] [CharP k 3] in

lemma eq_zero_of_forall_trace_mul (b : Module.Basis (Fin 2) k V) (h2 : (2 : k) ≠ 0) (X : slV k V)
    (hX : ∀ Y : slV k V, LinearMap.trace k V ((X : Module.End k V) * Y) = 0) : X = 0 := by
  classical
  set Xm : Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrix b b X with hXm
  have htr : Xm 0 0 + Xm 1 1 = 0 := by
    have := X.2
    rw [LinearMap.mem_ker, LinearMap.trace_eq_matrix_trace k b, Matrix.trace_fin_two] at this
    exact this

  have key : ∀ N : Matrix (Fin 2) (Fin 2) k, N.trace = 0 → (Xm * N).trace = 0 := by
    intro N hN
    have hmem : (LinearMap.toMatrix b b).symm N ∈ slV k V := by
      rw [LinearMap.mem_ker, LinearMap.trace_eq_matrix_trace k b, LinearEquiv.apply_symm_apply, hN]
    have := hX ⟨_, hmem⟩
    rw [LinearMap.trace_eq_matrix_trace k b, LinearMap.toMatrix_mul, LinearEquiv.apply_symm_apply] at this
    exact this
  have h10 : Xm 1 0 = 0 := by
    have := key !![0, 1; 0, 0] (by simp [Matrix.trace_fin_two])
    simpa [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : Xm 0 1 = 0 := by
    have := key !![0, 0; 1, 0] (by simp [Matrix.trace_fin_two])
    simpa [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h00 : Xm 0 0 = 0 := by
    have := key !![1, 0; 0, -1] (by simp [Matrix.trace_fin_two])
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at this
    have h2X : (2 : k) * Xm 0 0 = 0 := by linear_combination this + htr
    exact (mul_eq_zero.1 h2X).resolve_left h2
  have h11 : Xm 1 1 = 0 := by linear_combination htr - h00
  apply Subtype.ext
  apply (LinearMap.toMatrix b b).injective
  rw [← hXm, Submodule.coe_zero, map_zero]
  ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

lemma Φ_injective (b : Module.Basis (Fin 2) k V) [Module (ZMod 3) (slV k V)] :
    Function.Injective (Φ : slV k V →ₗ[ZMod 3] _) := by
  letI := ZMod.algebra k 3
  haveI : Module.Finite (ZMod 3) k := Module.Finite.of_finite
  rw [injective_iff_map_eq_zero]
  intro X hX
  apply eq_zero_of_forall_trace_mul b two_ne_zero'
  intro Y
  set t := LinearMap.trace k V ((X : Module.End k V) * Y) with ht
  apply (traceForm_nondegenerate (ZMod 3) k).1 t
  intro c
  rw [Algebra.traceForm_apply, mul_comm]
  have hcY : c • (Y : Module.End k V) ∈ slV k V := Submodule.smul_mem _ c Y.2
  have := LinearMap.congr_fun hX ⟨_, hcY⟩
  rw [Φ_apply, LinearMap.zero_apply] at this
  rw [ht, ← smul_eq_mul, ← map_smul, ← mul_smul_comm]
  exact this

omit [CharP k 3] in
lemma finite_slV (b : Module.Basis (Fin 2) k V) : Finite (slV k V) := by
  haveI := Module.Finite.of_basis b
  haveI : Finite (Module.End k V) := Module.finite_of_finite k
  infer_instance

lemma Φ_bijective (b : Module.Basis (Fin 2) k V) [Module (ZMod 3) (slV k V)] :
    Function.Bijective (Φ : slV k V →ₗ[ZMod 3] _) := by
  haveI := finite_slV b
  haveI : Module.Finite (ZMod 3) (slV k V) := Module.Finite.of_finite
  haveI : Finite (Module.Dual (ZMod 3) (slV k V)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 3) (slV k V) => (f : slV k V → ZMod 3))
      DFunLike.coe_injective
  haveI : Module.Finite (ZMod 3) (Module.Dual (ZMod 3) (slV k V)) := Module.Finite.of_finite
  refine ⟨Φ_injective b, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1
    (Φ_injective b)

end Nondeg

section Theta

variable {k : Type} [Field k] (F : Subfield k) {V : Type} [AddCommGroup V] [Module k V]
  (b : Module.Basis (Fin 2) k V) (g : GL (Fin 2) k)
  {S : Type} [Group S] (σ : S →* Module.End k V) (hσ : Function.Injective σ)
  (hσS : ∀ s : S, ∃ m : SL(2, F), LinearMap.toMatrix b b (σ s) =
      (g : Matrix (Fin 2) (Fin 2) k) *
        (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))
  (hSσ : ∀ m : SL(2, F), ∃ s : S, LinearMap.toMatrix b b (σ s) =
      (g : Matrix (Fin 2) (Fin 2) k) *
        (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))

abbrev Mk (m : SL(2, F)) : Matrix (Fin 2) (Fin 2) k :=
  (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k)

lemma Mk_mul (m m' : SL(2, F)) :
    (Matrix.SpecialLinearGroup.map F.subtype (m * m') : Matrix (Fin 2) (Fin 2) k) =
      (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
        (Matrix.SpecialLinearGroup.map F.subtype m' : Matrix (Fin 2) (Fin 2) k) := by
  rw [map_mul, Matrix.SpecialLinearGroup.coe_mul]

lemma conj_mul_conj (A B : Matrix (Fin 2) (Fin 2) k) :
    ((g : Matrix (Fin 2) (Fin 2) k) * A * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) *
      ((g : Matrix (Fin 2) (Fin 2) k) * B * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) =
      (g : Matrix (Fin 2) (Fin 2) k) * (A * B) * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  simp only [mul_assoc, Units.inv_mul_cancel_left]

include hσ in
lemma eq_of_toMatrix_eq {s s' : S} (h : LinearMap.toMatrix b b (σ s) = LinearMap.toMatrix b b (σ s')) :
    s = s' := hσ ((LinearMap.toMatrix b b).injective h)

noncomputable def θ : SL(2, F) →* S :=
  MonoidHom.mk' (fun m => Classical.choose (hSσ m)) (fun m m' => by
    apply eq_of_toMatrix_eq b σ hσ
    rw [Classical.choose_spec (hSσ (m * m')), map_mul σ, LinearMap.toMatrix_mul,
      Classical.choose_spec (hSσ m), Classical.choose_spec (hSσ m'), conj_mul_conj, Mk_mul])

lemma toMatrix_θ (m : SL(2, F)) : LinearMap.toMatrix b b (σ (θ F b g σ hσ hSσ m)) =
    (g : Matrix (Fin 2) (Fin 2) k) * Mk F m * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) :=
  Classical.choose_spec (hSσ m)

include hσS in
lemma θ_surjective : Function.Surjective (θ F b g σ hσ hSσ) := by
  intro s
  obtain ⟨m, hm⟩ := hσS s
  exact ⟨m, eq_of_toMatrix_eq b σ hσ (by rw [toMatrix_θ, hm])⟩

end Theta

section ConjK

variable {k : Type} [Field k] (F : Subfield k)

noncomputable abbrev sl2k : Submodule F (Matrix (Fin 2) (Fin 2) k) :=
  (LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)).restrictScalars F

lemma Mk_eq_map (m : SL(2, F)) : Mk F m = (m : Matrix (Fin 2) (Fin 2) F).map (algebraMap F k) := rfl

lemma Mk_inv_mul (m : SL(2, F)) :
    (Matrix.SpecialLinearGroup.map F.subtype m⁻¹ : Matrix (Fin 2) (Fin 2) k) *
      (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) = 1 := by
  rw [← Mk_mul, inv_mul_cancel, map_one, Matrix.SpecialLinearGroup.coe_one]

lemma Mk_mul_inv (m : SL(2, F)) :
    (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
      (Matrix.SpecialLinearGroup.map F.subtype m⁻¹ : Matrix (Fin 2) (Fin 2) k) = 1 := by
  rw [← Mk_mul, mul_inv_cancel, map_one, Matrix.SpecialLinearGroup.coe_one]

lemma conjK_mem (m : SL(2, F)) (N : Matrix (Fin 2) (Fin 2) k) (hN : N ∈ sl2k F) :
    Mk F m * N * Mk F m⁻¹ ∈ sl2k F := by
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hN ⊢
  rw [Matrix.trace_mul_comm, ← mul_assoc, Mk_inv_mul, one_mul, hN]

noncomputable def conjK : Representation F SL(2, F) (sl2k (k := k) F) where
  toFun m :=
    { toFun := fun N => ⟨Mk F m * N * Mk F m⁻¹, conjK_mem F m N N.2⟩
      map_add' := fun X Y => by
        apply Subtype.ext
        simp [mul_add, add_mul]
      map_smul' := fun r X => by
        apply Subtype.ext
        change Mk F m * (r • (X : Matrix (Fin 2) (Fin 2) k)) * Mk F m⁻¹ = r • (Mk F m * X * Mk F m⁻¹)
        rw [Matrix.mul_smul, Matrix.smul_mul] }
  map_one' := by
    refine LinearMap.ext fun X => Subtype.ext ?_
    simp [Mk]
  map_mul' m m' := by
    refine LinearMap.ext fun X => Subtype.ext ?_
    simp only [_root_.mul_inv_rev, Mk_mul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    simp only [mul_assoc]

lemma conjK_apply_coe (m : SL(2, F)) (N : sl2k (k := k) F) :
    ((conjK F m N : sl2k (k := k) F) : Matrix (Fin 2) (Fin 2) k) = Mk F m * N * Mk F m⁻¹ := rfl

variable [Finite k] [CharP k 3]

lemma exists_of_conjK (z : cocycles₁ (Rep.of (conjK (k := k) F))) :
    ∃ C : sl2k (k := k) F, ∀ m : SL(2, F), z m = conjK F m C - C := by
  haveI : CharP F 3 := (F.subtype.charP_iff_charP 3).2 inferInstance
  haveI : Subsingleton (H1 (Rep.of (conjK (k := k) F))) :=
    groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three
      (Rep.of (conjK (k := k) F)) (Submodule.subtype _) Subtype.val_injective (Submodule.range_subtype _)
      (fun m a => rfl)
  exact exists_eq_sub_of_subsingleton_H1 _ z

end ConjK

section Main

variable {k : Type} [Field k] [Finite k] [CharP k 3] (F : Subfield k)
  {V : Type} [AddCommGroup V] [Module k V] (b : Module.Basis (Fin 2) k V) (g : GL (Fin 2) k)
  {S : Type} [Group S] (σ : S →* Module.End k V) (hσ : Function.Injective σ)
  (hσS : ∀ s : S, ∃ m : SL(2, F), LinearMap.toMatrix b b (σ s) =
      (g : Matrix (Fin 2) (Fin 2) k) *
        (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))
  (hSσ : ∀ m : SL(2, F), ∃ s : S, LinearMap.toMatrix b b (σ s) =
      (g : Matrix (Fin 2) (Fin 2) k) *
        (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))

include hσ hσS hSσ in
theorem main [Module (ZMod 3) (slV k V)] (A : Rep.{0} (ZMod 3) S)
    (e : A ≃ₗ[ZMod 3] Module.Dual (ZMod 3) (slV k V))
    (he : ∀ (s : S) (a : A) (X Y : slV k V),
      (Y : Module.End k V) = σ s⁻¹ * X * σ s → e (A.ρ s a) X = e a Y) :
    Subsingleton (H1 A) := by
  classical

  have hθ := toMatrix_θ F b g σ hσ hSσ
  have hθsurj := θ_surjective F b g σ hσ hσS hSσ

  let ΦE : slV k V ≃ₗ[ZMod 3] Module.Dual (ZMod 3) (slV k V) :=
    LinearEquiv.ofBijective Φ (Φ_bijective b)
  have hΦE : ∀ X, ΦE X = Φ X := fun X => rfl
  have he' : ∀ (s : S) (a : A) (Y : slV k V), e (A.ρ s a) Y = e a (ad σ s⁻¹ Y) :=
    fun s a Y => he s a Y (ad σ s⁻¹ Y) (by rw [ad_coe, inv_inv])
  apply subsingleton_H1_of_forall
  intro x
  have hxcoc := (mem_cocycles₁_iff x).1 x.2

  set y : S → slV k V := fun s => ΦE.symm (e (x s)) with hy
  have hΦy : ∀ s, Φ (y s) = e (x s) := fun s => by
    rw [hy, ← hΦE, LinearEquiv.apply_symm_apply]
  have hycoc : ∀ s t, y (s * t) = ad σ s (y t) + y s := by
    intro s t
    apply Φ_injective b
    apply LinearMap.ext
    intro Y
    rw [hΦy, map_add, LinearMap.add_apply, Φ_ad, hΦy, hΦy, hxcoc, map_add, LinearMap.add_apply, he']

  have htrconj : ∀ Z : Module.End k V,
      (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * LinearMap.toMatrix b b Z *
        (g : Matrix (Fin 2) (Fin 2) k)).trace = LinearMap.trace k V Z := by
    intro Z
    rw [Matrix.trace_mul_cycle, Units.mul_inv, one_mul, ← LinearMap.trace_eq_matrix_trace k b]
  have hYmem : ∀ m : SL(2, F),
      ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        LinearMap.toMatrix b b (y (θ F b g σ hσ hSσ m) : Module.End k V) *
          (g : Matrix (Fin 2) (Fin 2) k) ∈ sl2k F := by
    intro m
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, Matrix.traceLinearMap_apply, htrconj]
    exact (y _).2
  let z : cocycles₁ (Rep.of (conjK (k := k) F)) :=
    ⟨fun m => ⟨_, hYmem m⟩, by
      rw [mem_cocycles₁_iff]
      intro m m'
      apply Subtype.ext
      rw [Submodule.coe_add]
      change ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        LinearMap.toMatrix b b (y (θ F b g σ hσ hSσ (m * m')) : Module.End k V) *
          (g : Matrix (Fin 2) (Fin 2) k) =
        (conjK F m ⟨_, hYmem m'⟩ : Matrix (Fin 2) (Fin 2) k) +
        ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
          LinearMap.toMatrix b b (y (θ F b g σ hσ hSσ m) : Module.End k V) * (g : Matrix (Fin 2) (Fin 2) k)
      rw [conjK_apply_coe, map_mul, hycoc, Submodule.coe_add, map_add, ad_coe, LinearMap.toMatrix_mul,
        LinearMap.toMatrix_mul, ← map_inv, hθ, hθ, Matrix.mul_add, Matrix.add_mul]
      congr 1
      simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]⟩
  obtain ⟨C, hC⟩ := exists_of_conjK F z

  have hZ₀mem : (LinearMap.toMatrix b b).symm ((g : Matrix (Fin 2) (Fin 2) k) * (C : Matrix (Fin 2) (Fin 2) k) *
      ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) ∈ slV k V := by
    have hC2 := C.2
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hC2
    rw [LinearMap.mem_ker, LinearMap.trace_eq_matrix_trace k b, LinearEquiv.apply_symm_apply,
      Matrix.trace_mul_cycle, Units.inv_mul, one_mul, hC2]
  set Z₀ : slV k V := ⟨_, hZ₀mem⟩ with hZ₀
  have hyZ : ∀ s, y s = ad σ s Z₀ - Z₀ := by
    intro s
    obtain ⟨m, rfl⟩ := hθsurj s
    have h1 := congrArg Subtype.val (hC m)
    rw [Submodule.coe_sub, conjK_apply_coe] at h1
    change ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        LinearMap.toMatrix b b (y (θ F b g σ hσ hSσ m) : Module.End k V) * (g : Matrix (Fin 2) (Fin 2) k) =
      (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) * C *
        (Matrix.SpecialLinearGroup.map F.subtype m⁻¹ : Matrix (Fin 2) (Fin 2) k) - C at h1
    have h2 : LinearMap.toMatrix b b (y (θ F b g σ hσ hSσ m) : Module.End k V) =
        (g : Matrix (Fin 2) (Fin 2) k) *
          ((Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) * C *
            (Matrix.SpecialLinearGroup.map F.subtype m⁻¹ : Matrix (Fin 2) (Fin 2) k) - C) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
      rw [← h1]
      simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
    apply Subtype.ext
    apply (LinearMap.toMatrix b b).injective
    rw [h2, Submodule.coe_sub, map_sub, ad_coe, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul,
      ← map_inv, hθ, hθ, hZ₀]
    change _ = (g : Matrix (Fin 2) (Fin 2) k) * (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
        ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        LinearMap.toMatrix b b ((LinearMap.toMatrix b b).symm ((g : Matrix (Fin 2) (Fin 2) k) *
          (C : Matrix (Fin 2) (Fin 2) k) * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))) *
        ((g : Matrix (Fin 2) (Fin 2) k) * (Matrix.SpecialLinearGroup.map F.subtype m⁻¹ : Matrix (Fin 2) (Fin 2) k) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) -
        LinearMap.toMatrix b b ((LinearMap.toMatrix b b).symm ((g : Matrix (Fin 2) (Fin 2) k) *
          (C : Matrix (Fin 2) (Fin 2) k) * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)))
    rw [LinearEquiv.apply_symm_apply, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    simp only [mul_assoc, Units.inv_mul_cancel_left]

  refine ⟨e.symm (Φ Z₀), fun s => e.injective ?_⟩
  apply LinearMap.ext
  intro Y
  rw [map_sub, LinearMap.sub_apply, he', e.apply_symm_apply, ← hΦy, hyZ, map_sub, LinearMap.sub_apply,
    Φ_ad]

end Main

end P2mCoefSL
p2m_reactivate "P2MW.S_groupCohomology_subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map.P2mCoefSL"

open P2mCoefSL in
theorem solution
    {k : Type} [Field k] [Finite k] [CharP k 3] (F : Subfield k)
    {V : Type} [AddCommGroup V] [Module k V] (b : Module.Basis (Fin 2) k V)
    (g : GL (Fin 2) k)
    {S : Type} [Group S] (σ : S →* Module.End k V) (hσ : Function.Injective σ)
    (hσS : ∀ s : S, ∃ m : SL(2, F), LinearMap.toMatrix b b (σ s) =
      (g : Matrix (Fin 2) (Fin 2) k) *
        (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))
    (hSσ : ∀ m : SL(2, F), ∃ s : S, LinearMap.toMatrix b b (σ s) =
      (g : Matrix (Fin 2) (Fin 2) k) *
        (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))
    [Module (ZMod 3) (LinearMap.ker (LinearMap.trace k V))]
    (A : Rep (ZMod 3) S)
    (e : A ≃ₗ[ZMod 3] Module.Dual (ZMod 3) (LinearMap.ker (LinearMap.trace k V)))
    (he : ∀ (s : S) (a : A) (X Y : LinearMap.ker (LinearMap.trace k V)),
      (Y : Module.End k V) = σ s⁻¹ * X * σ s → e (A.ρ s a) X = e a Y) :
    Subsingleton (H1 A) :=
  main F b g σ hσ hσS hSσ A e he

end S_groupCohomology_subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map
end P2MW
export P2MW.S_groupCohomology_subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map (solution)
