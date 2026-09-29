-- Prove2me | solution 1 for groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9a63cd9d-b00b-50e0-95f8-d0875ee4d0d5

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_CorestrictionFin
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three.groupCohomology groupCohomology.Cores P2MW.S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three.groupCohomology.Cores"

namespace groupCohomology
p2m_export "groupCohomology" "congr cocycles inhomogeneousCochains.d_def inhomogeneousCochains Cores.Transversal Cores.Transversal.nonempty"
p2m_open "groupCohomology"
namespace Cores
p2m_export "groupCohomology.Cores" "IsSlotInvariant resFin corFin Transversal Transversal.nonempty Transversal.qinv fintypeQuot"
p2m_open "groupCohomology.Cores"

variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex] (A : Rep.{0} k G) (τ : Transversal H)

attribute [local instance] fintypeQuot

def hvec {n : ℕ} (q : G ⧸ H) (g : Fin n → G) : Fin n → H := fun i =>
  (τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g (Fin.castSucc i)))⁻¹ * τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g i.succ)

omit [H.FiniteIndex] in
lemma hvec_apply {n : ℕ} (q : G ⧸ H) (g : Fin n → G) (i : Fin n) :
    hvec τ q g i = (τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g (Fin.castSucc i)))⁻¹
      * τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g i.succ) := rfl

lemma corFin_eq_sum_hvec (n : ℕ) (u : (Fin n → H) → A) (g : Fin n → G) :
    corFin A τ n u g = ∑ q : G ⧸ H, A.ρ (τ.σ q) (u (hvec τ q g)) := rfl

omit [H.FiniteIndex] in

lemma partialProd_hvec {n : ℕ} (q : G ⧸ H) (g : Fin n → G) (m : Fin (n + 1)) :
    Fin.partialProd (hvec τ q g) m = τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g m) := by
  induction m using Fin.induction with
  | zero =>
    rw [Fin.partialProd_zero, Fin.partialProd_zero, mul_one]
    exact Subtype.ext (τ.coe_lam_σ_inv q).symm
  | succ i ih =>
    rw [Fin.partialProd_succ, ih, hvec_apply, mul_inv_cancel_left]

omit [H.FiniteIndex] in

lemma hvec_contractNth {n : ℕ} (q : G ⧸ H) (g : Fin (n + 1) → G) (j : Fin (n + 1)) :
    hvec τ q (Fin.contractNth j (· * ·) g) = Fin.contractNth j (· * ·) (hvec τ q g) := by
  funext k
  rw [← Fin.inv_partialProd_mul_eq_contractNth (hvec τ q g) j k, partialProd_hvec, partialProd_hvec, hvec_apply,
    Fin.partialProd_contractNth, Function.comp_apply, Function.comp_apply, Fin.succ_succAbove_succ]

omit [H.FiniteIndex] in

lemma hvec_succ {n : ℕ} (q : G ⧸ H) (g : Fin (n + 1) → G) (i : Fin n) :
    hvec τ q g i.succ = hvec τ ((g 0)⁻¹ • q) (fun i => g i.succ) i := by
  have key : ∀ j : Fin (n + 1), τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g j.succ) =
      τ.lam ((τ.σ q)⁻¹ * g 0) * τ.lam ((τ.σ ((g 0)⁻¹ • q))⁻¹ * Fin.partialProd (fun i => g i.succ) j) := by
    intro j
    rw [Fin.partialProd_succ' g j, ← mul_assoc, τ.lam_mul ((τ.σ q)⁻¹ * g 0), τ.qinv_σ_inv_mul]
    rfl
  rw [hvec_apply, hvec_apply, ← Fin.succ_castSucc, key (Fin.castSucc i), key i.succ, mul_inv_rev, mul_assoc,
    inv_mul_cancel_left]

omit [H.FiniteIndex] in

lemma mul_σ_inv_smul_eq {n : ℕ} (q : G ⧸ H) (g : Fin (n + 1) → G) :
    g 0 * τ.σ ((g 0)⁻¹ • q) = τ.σ q * (hvec τ q g 0 : G) := by
  have hP1 : Fin.partialProd g (0 : Fin (n + 1)).succ = g 0 := by
    rw [Fin.partialProd_succ, Fin.castSucc_zero, Fin.partialProd_zero, one_mul]
  have h1 : (hvec τ q g 0 : G) = τ.lam ((τ.σ q)⁻¹ * g 0) := by
    rw [hvec_apply, Subgroup.coe_mul, InvMemClass.coe_inv, Fin.castSucc_zero, Fin.partialProd_zero, mul_one,
      τ.coe_lam_σ_inv, inv_one, one_mul, hP1]
  rw [h1, τ.mul_σ]

theorem corFin_d_aux (n : ℕ) (u : (Fin n → H) → A) :
    corFin A τ (n + 1) (((inhomogeneousCochains (Rep.res H.subtype A)).d n (n + 1)).hom u)
      = ((inhomogeneousCochains A).d n (n + 1)).hom (corFin A τ n u) := by
  funext g
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
  simp only [corFin_eq_sum_hvec, inhomogeneousCochains.d_hom_apply]
  have hres : ∀ (h : H) (a : A), (Rep.res H.subtype A).ρ h a = A.ρ (h : G) a := fun _ _ => rfl
  simp only [hres, map_add, map_sum, map_smul, Finset.sum_add_distrib]
  congr 1
  ·
    have hsum : ∀ q : G ⧸ H, A.ρ (τ.σ q) (A.ρ ((hvec τ q g 0 : H) : G) (u fun i => hvec τ q g i.succ)) =
        A.ρ (g 0) (A.ρ (τ.σ ((g 0)⁻¹ • q)) (u (hvec τ ((g 0)⁻¹ • q) fun i => g i.succ))) := by
      intro q
      have hx : (fun i => hvec τ q g i.succ) = hvec τ ((g 0)⁻¹ • q) (fun i => g i.succ) :=
        funext (hvec_succ τ q g)
      rw [hx, ← Module.End.mul_apply, ← map_mul, ← mul_σ_inv_smul_eq τ q g, map_mul, Module.End.mul_apply]
    simp only [hsum]
    exact Fintype.sum_equiv (MulAction.toPerm (g 0)⁻¹) _ _ (fun q => rfl)
  ·
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hvec_contractNth]

section SlotInv

variable {U : Subgroup G} [U.Normal]

omit [H.FiniteIndex] in
lemma qinv_mul_of_mem (hUH : U ≤ H) (z : G) {ν : G} (hν : ν ∈ U) :
    Transversal.qinv (H := H) (z * ν) = Transversal.qinv (H := H) z := by
  rw [Transversal.qinv, Transversal.qinv, QuotientGroup.eq, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv]

  exact hUH (Subgroup.Normal.conj_mem inferInstance ν hν z)

omit [H.FiniteIndex] in
lemma coe_lam_mul_of_mem (hUH : U ≤ H) (z : G) {ν : G} (hν : ν ∈ U) :
    (τ.lam (z * ν) : G) = τ.lam z * ((τ.σ (Transversal.qinv (H := H) z))⁻¹ * ν * τ.σ (Transversal.qinv (H := H) z)) := by
  rw [τ.coe_lam, τ.coe_lam, qinv_mul_of_mem hUH z hν]
  group

omit [H.FiniteIndex] in
lemma inv_mul_mul_mem {ν : G} (c : G) (hν : ν ∈ U) : c⁻¹ * ν * c ∈ U := by
  simpa using Subgroup.Normal.conj_mem inferInstance ν hν c⁻¹

omit [H.FiniteIndex] in
lemma exists_partialProd_mul_eq {n : ℕ} (g s : Fin n → G) (hs : ∀ i, s i ∈ U) (m : Fin (n + 1)) :
    ∃ ν ∈ U, Fin.partialProd (g * s) m = Fin.partialProd g m * ν := by
  induction m using Fin.induction with
  | zero => exact ⟨1, U.one_mem, by rw [Fin.partialProd_zero, Fin.partialProd_zero, mul_one]⟩
  | succ i ih =>
    obtain ⟨ν, hν, e⟩ := ih
    refine ⟨(g i)⁻¹ * ν * g i * s i, U.mul_mem (inv_mul_mul_mem (g i) hν) (hs i), ?_⟩
    rw [Fin.partialProd_succ, Fin.partialProd_succ, e, Pi.mul_apply]
    group

omit [H.FiniteIndex] in
lemma exists_coe_partialProd_hvec_mul (hUH : U ≤ H) {n : ℕ} (q : G ⧸ H) (g s : Fin n → G)
    (hs : ∀ i, s i ∈ U) (m : Fin (n + 1)) :
    ∃ ν ∈ U, ((Fin.partialProd (hvec τ q (g * s)) m : H) : G) = ((Fin.partialProd (hvec τ q g) m : H) : G) * ν := by
  rw [partialProd_hvec, partialProd_hvec]
  obtain ⟨ν, hν, e⟩ := exists_partialProd_mul_eq g s hs m
  rw [e, ← mul_assoc, coe_lam_mul_of_mem τ hUH _ hν]
  exact ⟨_, inv_mul_mul_mem _ hν, rfl⟩

omit [H.FiniteIndex] in

lemma exists_hvec_mul_eq (hUH : U ≤ H) {n : ℕ} (q : G ⧸ H) (g s : Fin n → G) (hs : ∀ i, s i ∈ U) :
    ∃ t : Fin n → H, (∀ i, (t i : G) ∈ U) ∧ hvec τ q (g * s) = hvec τ q g * t := by
  refine ⟨fun i => (hvec τ q g i)⁻¹ * hvec τ q (g * s) i, fun i => ?_,
    by funext i; rw [Pi.mul_apply, mul_inv_cancel_left]⟩
  obtain ⟨ν₁, h₁, f₁⟩ := exists_coe_partialProd_hvec_mul τ hUH q g s hs (Fin.castSucc i)
  obtain ⟨ν₂, h₂, f₂⟩ := exists_coe_partialProd_hvec_mul τ hUH q g s hs i.succ
  dsimp only
  rw [← Fin.partialProd_right_inv (hvec τ q g) i, ← Fin.partialProd_right_inv (hvec τ q (g * s)) i]
  set a : G := ((Fin.partialProd (hvec τ q g) (Fin.castSucc i) : H) : G) with ha
  set b : G := ((Fin.partialProd (hvec τ q g) i.succ : H) : G) with hb
  have key : ((((Fin.partialProd (hvec τ q g) (Fin.castSucc i))⁻¹ * Fin.partialProd (hvec τ q g) i.succ)⁻¹ *
      ((Fin.partialProd (hvec τ q (g * s)) (Fin.castSucc i))⁻¹ * Fin.partialProd (hvec τ q (g * s)) i.succ) : H) : G)
      = (b⁻¹ * a) * ν₁⁻¹ * (b⁻¹ * a)⁻¹ * ν₂ := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [f₁, f₂, ← ha, ← hb]
    group
  rw [key]
  exact U.mul_mem (Subgroup.Normal.conj_mem inferInstance _ (U.inv_mem h₁) _) h₂

theorem isSlotInvariant_corFin_aux (n : ℕ) (U : Subgroup G) [U.Normal] (hUH : U ≤ H)
    (u : (Fin n → H) → A) (hu : IsSlotInvariant (U.comap H.subtype) u) :
    IsSlotInvariant U (corFin A τ n u) := by
  intro g s hs
  rw [corFin_eq_sum_hvec, corFin_eq_sum_hvec]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨t, ht, e⟩ := exists_hvec_mul_eq τ hUH q g s hs
  rw [e, hu _ _ (fun i => ht i)]

end SlotInv

end Cores
end groupCohomology

namespace groupCohomology
p2m_export "groupCohomology" "congr cocycles inhomogeneousCochains.d_def inhomogeneousCochains Cores.Transversal Cores.Transversal.nonempty"
p2m_open "groupCohomology"
namespace Cores
p2m_export "groupCohomology.Cores" "IsSlotInvariant resFin corFin Transversal Transversal.nonempty Transversal.qinv fintypeQuot"
p2m_open "groupCohomology.Cores"

section DFormulas
variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)

lemma d23_apply (b : (Fin 2 → G) → A) (a c e : G) :
    ((inhomogeneousCochains A).d 2 3).hom b ![a, c, e]
      = A.ρ a (b ![c, e]) - b ![a * c, e] + b ![a, c * e] - b ![a, c] := by
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_hom_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  have e0 : (fun i : Fin 2 => (![a, c, e] : Fin 3 → G) i.succ) = ![c, e] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth (0 : Fin 3) (· * ·) (![a, c, e] : Fin 3 → G) = ![a * c, e] := by
    funext i; fin_cases i <;> simp [Fin.contractNth]
  have e2 : Fin.contractNth (1 : Fin 3) (· * ·) (![a, c, e] : Fin 3 → G) = ![a, c * e] := by
    funext i; fin_cases i <;> simp [Fin.contractNth]
  have e3 : Fin.contractNth (2 : Fin 3) (· * ·) (![a, c, e] : Fin 3 → G) = ![a, c] := by
    funext i; fin_cases i <;> simp [Fin.contractNth]
  rw [e0, e1, e2, e3]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_succ, pow_zero, one_mul, mul_neg, mul_one, neg_neg,
    neg_smul, one_smul]
  abel

lemma d34_apply (f : (Fin 3 → G) → A) (a c e r : G) :
    ((inhomogeneousCochains A).d 3 4).hom f ![a, c, e, r]
      = A.ρ a (f ![c, e, r]) - f ![a * c, e, r] + f ![a, c * e, r] - f ![a, c, e * r] + f ![a, c, e] := by
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_hom_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  have e0 : (fun i : Fin 3 => (![a, c, e, r] : Fin 4 → G) i.succ) = ![c, e, r] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth (0 : Fin 4) (· * ·) (![a, c, e, r] : Fin 4 → G) = ![a * c, e, r] := by
    funext i; fin_cases i <;> simp [Fin.contractNth]
  have e2 : Fin.contractNth (1 : Fin 4) (· * ·) (![a, c, e, r] : Fin 4 → G) = ![a, c * e, r] := by
    funext i; fin_cases i <;> simp [Fin.contractNth]
  have e3 : Fin.contractNth (2 : Fin 4) (· * ·) (![a, c, e, r] : Fin 4 → G) = ![a, c, e * r] := by
    funext i; fin_cases i <;> simp [Fin.contractNth]
  have e4 : Fin.contractNth (3 : Fin 4) (· * ·) (![a, c, e, r] : Fin 4 → G) = ![a, c, e] := by
    funext i; fin_cases i <;> simp [Fin.contractNth]
  have e33 : ((2 : Fin 3).succ : Fin 4) = 3 := rfl
  simp only [e33]
  rw [e0, e1, e2, e3, e4]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl, pow_succ, pow_zero,
    one_mul, mul_neg, mul_one, neg_neg, neg_smul, one_smul]
  abel

lemma core_identity (u : (Fin 3 → G) → A) (hu : ((inhomogeneousCochains A).d 3 4).hom u = 0)
    (x0 a c e x1 x2 x3 h0 h1 h2 : G) (r1 : x0 * a = h0 * x1) (r2 : x1 * c = h1 * x2) (r3 : x2 * e = h2 * x3) :
    A.ρ h0 (u ![x1, c, e] - u ![h1, x2, e] + u ![h1, h2, x3])
      - (u ![x0, a * c, e] - u ![h0 * h1, x2, e] + u ![h0 * h1, h2, x3])
      + (u ![x0, a, c * e] - u ![h0, x1, c * e] + u ![h0, h1 * h2, x3])
      - (u ![x0, a, c] - u ![h0, x1, c] + u ![h0, h1, x2])
    = -(u ![h0, h1, h2] - A.ρ x0 (u ![a, c, e])) := by
  have I1 : A.ρ x0 (u ![a, c, e]) - u ![x0 * a, c, e] + u ![x0, a * c, e] - u ![x0, a, c * e] + u ![x0, a, c] = 0 := by
    rw [← d34_apply, hu]; rfl
  have I2 : A.ρ h0 (u ![x1, c, e]) - u ![h0 * x1, c, e] + u ![h0, x1 * c, e] - u ![h0, x1, c * e] + u ![h0, x1, c] = 0 := by
    rw [← d34_apply, hu]; rfl
  have I3 : A.ρ h0 (u ![h1, x2, e]) - u ![h0 * h1, x2, e] + u ![h0, h1 * x2, e] - u ![h0, h1, x2 * e] + u ![h0, h1, x2] = 0 := by
    rw [← d34_apply, hu]; rfl
  have I4 : A.ρ h0 (u ![h1, h2, x3]) - u ![h0 * h1, h2, x3] + u ![h0, h1 * h2, x3] - u ![h0, h1, h2 * x3] + u ![h0, h1, h2] = 0 := by
    rw [← d34_apply, hu]; rfl
  rw [r1] at I1
  rw [r2] at I2
  rw [r3] at I3
  simp only [map_sub, map_add]
  linear_combination (norm := abel) I2 - I1 - I3 + I4

end DFormulas

section Frames

variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G} (A : Rep.{0} k G) (τ : Transversal H)

lemma coe_hvec_eq {n : ℕ} (q : G ⧸ H) (g : Fin n → G) (i : Fin n) :
    (hvec τ q g i : G) = τ.lam ((τ.σ ((Fin.partialProd g (Fin.castSucc i))⁻¹ • q))⁻¹ * g i) := by
  rw [hvec_apply, Subgroup.coe_mul, InvMemClass.coe_inv, Fin.partialProd_succ, ← mul_assoc,
    τ.coe_lam_mul ((τ.σ q)⁻¹ * Fin.partialProd g (Fin.castSucc i)) (g i), τ.qinv_σ_inv_mul, inv_mul_cancel_left]

lemma frame_rel (q : G ⧸ H) (g : G) :
    (τ.σ q)⁻¹ * g = τ.lam ((τ.σ q)⁻¹ * g) * (τ.σ (g⁻¹ • q))⁻¹ := by
  conv_lhs => rw [← τ.lam_mul_σ_inv ((τ.σ q)⁻¹ * g), τ.qinv_σ_inv_mul]

lemma coe_lam_frame_mul (q : G ⧸ H) (g g' : G) :
    (τ.lam ((τ.σ q)⁻¹ * (g * g')) : G) = τ.lam ((τ.σ q)⁻¹ * g) * τ.lam ((τ.σ (g⁻¹ • q))⁻¹ * g') := by
  rw [← mul_assoc, τ.coe_lam_mul ((τ.σ q)⁻¹ * g) g', τ.qinv_σ_inv_mul]

lemma hvec2_zero (q : G ⧸ H) (v w : G) : (hvec τ q ![v, w] 0 : G) = τ.lam ((τ.σ q)⁻¹ * v) := by
  rw [coe_hvec_eq]; simp [Fin.partialProd_zero]
lemma hvec2_one (q : G ⧸ H) (v w : G) : (hvec τ q ![v, w] 1 : G) = τ.lam ((τ.σ (v⁻¹ • q))⁻¹ * w) := by
  rw [coe_hvec_eq]
  have : Fin.partialProd ![v, w] (Fin.castSucc 1) = v := by
    rw [show (Fin.castSucc (1 : Fin 2) : Fin 3) = (0 : Fin 2).succ from rfl, Fin.partialProd_succ, Fin.castSucc_zero,
      Fin.partialProd_zero, one_mul]; rfl
  rw [this]; rfl
lemma hvec3_zero (q : G ⧸ H) (a c e : G) : (hvec τ q ![a, c, e] 0 : G) = τ.lam ((τ.σ q)⁻¹ * a) := by
  rw [coe_hvec_eq]; simp [Fin.partialProd_zero]
lemma hvec3_one (q : G ⧸ H) (a c e : G) : (hvec τ q ![a, c, e] 1 : G) = τ.lam ((τ.σ (a⁻¹ • q))⁻¹ * c) := by
  rw [coe_hvec_eq]
  have : Fin.partialProd ![a, c, e] (Fin.castSucc 1) = a := by
    rw [show (Fin.castSucc (1 : Fin 3) : Fin 4) = (0 : Fin 3).succ from rfl, Fin.partialProd_succ, Fin.castSucc_zero,
      Fin.partialProd_zero, one_mul]; rfl
  rw [this]; rfl
lemma hvec3_two (q : G ⧸ H) (a c e : G) : (hvec τ q ![a, c, e] 2 : G) = τ.lam ((τ.σ (c⁻¹ • a⁻¹ • q))⁻¹ * e) := by
  rw [coe_hvec_eq]
  have : Fin.partialProd ![a, c, e] (Fin.castSucc 2) = a * c := by
    rw [show (Fin.castSucc (2 : Fin 3) : Fin 4) = (1 : Fin 3).succ from rfl, Fin.partialProd_succ,
      show (Fin.castSucc (1 : Fin 3) : Fin 4) = (0 : Fin 3).succ from rfl, Fin.partialProd_succ, Fin.castSucc_zero,
      Fin.partialProd_zero, one_mul]; rfl
  rw [this, mul_inv_rev, mul_smul]; rfl

end Frames

section CorRes3

variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex] (A : Rep.{0} k G) (τ : Transversal H)

attribute [local instance] fintypeQuot

noncomputable def beta (u : (Fin 3 → G) → A) (q : G ⧸ H) (v w : G) : A :=
  u ![(τ.σ q)⁻¹, v, w] - u ![τ.lam ((τ.σ q)⁻¹ * v), (τ.σ (v⁻¹ • q))⁻¹, w]
    + u ![τ.lam ((τ.σ q)⁻¹ * v), τ.lam ((τ.σ (v⁻¹ • q))⁻¹ * w), (τ.σ (w⁻¹ • v⁻¹ • q))⁻¹]

noncomputable def bFin3 (u : (Fin 3 → G) → A) : (Fin 2 → G) → A := fun g =>
  -∑ q : G ⧸ H, A.ρ (τ.σ q) (beta A τ u q (g 0) (g 1))

lemma bFin3_pair (u : (Fin 3 → G) → A) (v w : G) :
    bFin3 A τ u ![v, w] = -∑ q : G ⧸ H, A.ρ (τ.σ q) (beta A τ u q v w) := rfl

theorem d_bFin3 (u : (Fin 3 → G) → A) (hu : ((inhomogeneousCochains A).d 3 4).hom u = 0) (g : Fin 3 → G) :
    ((inhomogeneousCochains A).d 2 3).hom (bFin3 A τ u) g = corFin A τ 3 (resFin A 3 u) g - H.index • u g := by

  have hg : g = ![g 0, g 1, g 2] := by funext i; fin_cases i <;> rfl
  set a := g 0; set c := g 1; set e := g 2
  rw [hg, d23_apply, bFin3_pair, bFin3_pair, bFin3_pair, bFin3_pair, corFin_eq_sum_hvec]

  have hidx : H.index • u ![a, c, e] = ∑ q : G ⧸ H, A.ρ (τ.σ q) (A.ρ (τ.σ q)⁻¹ (u ![a, c, e])) := by
    rw [Finset.sum_congr rfl fun q _ => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply], Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]; rfl

  have hhead : A.ρ a (-∑ q : G ⧸ H, A.ρ (τ.σ q) (beta A τ u q c e)) =
      -∑ q : G ⧸ H, A.ρ (τ.σ q) (A.ρ (τ.lam ((τ.σ q)⁻¹ * a) : G) (beta A τ u (a⁻¹ • q) c e)) := by
    rw [map_neg, map_sum]
    congr 1
    symm
    refine (Fintype.sum_equiv (MulAction.toPerm a⁻¹) _ _ (fun q => ?_))
    show A.ρ (τ.σ q) (A.ρ (τ.lam ((τ.σ q)⁻¹ * a) : G) (beta A τ u (a⁻¹ • q) c e)) = A.ρ a (A.ρ (τ.σ (a⁻¹ • q)) (beta A τ u (a⁻¹ • q) c e))
    rw [← Module.End.mul_apply, ← map_mul, ← τ.mul_σ q a, map_mul, Module.End.mul_apply]
  rw [hhead, hidx, ← Finset.sum_sub_distrib]
  simp only [neg_sub_neg, sub_neg_eq_add, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib,
    ← map_add, ← map_sub, ← map_neg]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1

  set x0 : G := (τ.σ q)⁻¹ with hx0
  set h0 : G := (τ.lam (x0 * a) : G) with hh0
  set x1 : G := (τ.σ (a⁻¹ • q))⁻¹ with hx1
  set h1 : G := (τ.lam (x1 * c) : G) with hh1
  set x2 : G := (τ.σ (c⁻¹ • a⁻¹ • q))⁻¹ with hx2
  set h2 : G := (τ.lam (x2 * e) : G) with hh2
  set x3 : G := (τ.σ (e⁻¹ • c⁻¹ • a⁻¹ • q))⁻¹ with hx3
  have r1 : x0 * a = h0 * x1 := frame_rel τ q a
  have r2 : x1 * c = h1 * x2 := frame_rel τ (a⁻¹ • q) c
  have r3 : x2 * e = h2 * x3 := frame_rel τ (c⁻¹ • a⁻¹ • q) e
  have hv : (fun i => (hvec τ q ![a, c, e] i : G)) = ![h0, h1, h2] := by
    funext i; fin_cases i
    · exact hvec3_zero τ q a c e
    · exact hvec3_one τ q a c e
    · exact hvec3_two τ q a c e
  have e1 : (τ.lam (x0 * (a * c)) : G) = h0 * h1 := coe_lam_frame_mul τ q a c
  have e2 : (τ.lam (x1 * (c * e)) : G) = h1 * h2 := coe_lam_frame_mul τ (a⁻¹ • q) c e
  have c1 : (a * c)⁻¹ • q = c⁻¹ • a⁻¹ • q := by rw [mul_inv_rev, mul_smul]
  have c2 : (c * e)⁻¹ • a⁻¹ • q = e⁻¹ • c⁻¹ • a⁻¹ • q := by rw [mul_inv_rev, mul_smul]
  have c3 : e⁻¹ • (a * c)⁻¹ • q = e⁻¹ • c⁻¹ • a⁻¹ • q := by rw [c1]
  simp only [resFin, hv, beta, ← hx0, ← hx1, c1, c2, c3, ← hx2, ← hx3, e1, e2, ← hh0, ← hh1, ← hh2]
  have key := core_identity A u hu x0 a c e x1 x2 x3 h0 h1 h2 r1 r2 r3
  simp only [map_sub, map_add, map_neg] at key ⊢

  linear_combination (norm := abel) -key

omit [H.FiniteIndex] in
lemma inv_smul_coset_eq {U : Subgroup G} [U.Normal] (hUH : U ≤ H) {ν : G} (hν : ν ∈ U) (r : G ⧸ H) :
    ν⁻¹ • r = r := by
  induction r using QuotientGroup.induction_on with
  | H z =>
    show (((ν⁻¹ * z : G)) : G ⧸ H) = (z : G ⧸ H)
    rw [QuotientGroup.eq, mul_inv_rev, inv_inv]
    exact hUH (by simpa using Subgroup.Normal.conj_mem inferInstance ν hν z⁻¹)

omit [H.FiniteIndex] in
lemma mul_inv_smul_eq {U : Subgroup G} [U.Normal] (hUH : U ≤ H) (g : G) {ν : G} (hν : ν ∈ U) (r : G ⧸ H) :
    (g * ν)⁻¹ • r = g⁻¹ • r := by
  rw [mul_inv_rev, mul_smul, inv_smul_coset_eq hUH hν]

omit [H.FiniteIndex] in
lemma vec3_mul (a b c a' b' c' : G) : (![a, b, c] : Fin 3 → G) * ![a', b', c'] = ![a * a', b * b', c * c'] := by
  funext i; fin_cases i <;> rfl

omit [H.FiniteIndex] in
lemma beta_mul {U : Subgroup G} [U.Normal] (hUH : U ≤ H) (u : (Fin 3 → G) → A) (hu : IsSlotInvariant U u)
    (q : G ⧸ H) (v w s0 s1 : G) (hs0 : s0 ∈ U) (hs1 : s1 ∈ U) :
    beta A τ u q (v * s0) (w * s1) = beta A τ u q v w := by

  have l0 := coe_lam_mul_of_mem τ hUH ((τ.σ q)⁻¹ * v) hs0
  have l1 := coe_lam_mul_of_mem τ hUH ((τ.σ (v⁻¹ • q))⁻¹ * w) hs1
  set t0 : G := (τ.σ (Transversal.qinv (H := H) ((τ.σ q)⁻¹ * v)))⁻¹ * s0 * τ.σ (Transversal.qinv (H := H) ((τ.σ q)⁻¹ * v))
  set t1 : G := (τ.σ (Transversal.qinv (H := H) ((τ.σ (v⁻¹ • q))⁻¹ * w)))⁻¹ * s1 *
    τ.σ (Transversal.qinv (H := H) ((τ.σ (v⁻¹ • q))⁻¹ * w))
  have ht0 : t0 ∈ U := inv_mul_mul_mem _ hs0
  have ht1 : t1 ∈ U := inv_mul_mul_mem _ hs1
  simp only [beta]
  rw [mul_inv_smul_eq hUH v hs0, mul_inv_smul_eq hUH w hs1, ← mul_assoc, l0, ← mul_assoc ((τ.σ (v⁻¹ • q))⁻¹), l1]
  have e1 : (![(τ.σ q)⁻¹, v * s0, w * s1] : Fin 3 → G) = ![(τ.σ q)⁻¹, v, w] * ![1, s0, s1] := by
    rw [vec3_mul, mul_one]
  have e2 : (![(τ.lam ((τ.σ q)⁻¹ * v) : G) * t0, (τ.σ (v⁻¹ • q))⁻¹, w * s1] : Fin 3 → G)
      = ![(τ.lam ((τ.σ q)⁻¹ * v) : G), (τ.σ (v⁻¹ • q))⁻¹, w] * ![t0, 1, s1] := by
    rw [vec3_mul, mul_one]
  have e3 : (![(τ.lam ((τ.σ q)⁻¹ * v) : G) * t0, (τ.lam ((τ.σ (v⁻¹ • q))⁻¹ * w) : G) * t1, (τ.σ (w⁻¹ • v⁻¹ • q))⁻¹] : Fin 3 → G)
      = ![(τ.lam ((τ.σ q)⁻¹ * v) : G), (τ.lam ((τ.σ (v⁻¹ • q))⁻¹ * w) : G), (τ.σ (w⁻¹ • v⁻¹ • q))⁻¹] * ![t0, t1, 1] := by
    rw [vec3_mul, mul_one]
  rw [e1, e2, e3, hu _ _ (by intro i; fin_cases i <;> simp [ht0, ht1, hs0, hs1, U.one_mem]),
    hu _ _ (by intro i; fin_cases i <;> simp [ht0, ht1, hs0, hs1, U.one_mem]),
    hu _ _ (by intro i; fin_cases i <;> simp [ht0, ht1, hs0, hs1, U.one_mem])]

lemma isSlotInvariant_bFin3 (U : Subgroup G) [U.Normal] (hUH : U ≤ H) (u : (Fin 3 → G) → A)
    (hu : IsSlotInvariant U u) : IsSlotInvariant U (bFin3 A τ u) := by
  intro g s hs
  show -(∑ q : G ⧸ H, A.ρ (τ.σ q) (beta A τ u q ((g * s) 0) ((g * s) 1))) = -(∑ q : G ⧸ H, A.ρ (τ.σ q) (beta A τ u q (g 0) (g 1)))
  simp only [Pi.mul_apply, beta_mul A τ hUH u hu _ _ _ _ _ (hs 0) (hs 1)]

theorem exists_d_eq_corFin_resFin_sub_index_smul_three_aux (u : (Fin 3 → G) → A)
    (hu : ((inhomogeneousCochains A).d 3 4).hom u = 0) :
    ∃ b : (Fin 2 → G) → A,
      ((inhomogeneousCochains A).d 2 3).hom b = corFin A τ 3 (resFin A 3 u) - H.index • u ∧
      ∀ U : Subgroup G, U.Normal → U ≤ H → IsSlotInvariant U u → IsSlotInvariant U b := by
  refine ⟨bFin3 A τ u, ?_, fun U hN hUH hinv => ?_⟩
  · funext g
    rw [d_bFin3 A τ u hu g, Pi.sub_apply, Pi.smul_apply]
  · haveI := hN
    exact isSlotInvariant_bFin3 A τ U hUH u hinv

omit [H.FiniteIndex] in
lemma isSlotInvariant_sub {n : ℕ} {U : Subgroup G} {f g : (Fin n → G) → A}
    (hf : IsSlotInvariant U f) (hg : IsSlotInvariant U g) : IsSlotInvariant U (f - g) := by
  intro x s hs; simp only [Pi.sub_apply, hf x s hs, hg x s hs]

omit [H.FiniteIndex] in
lemma isSlotInvariant_smul {n : ℕ} {U : Subgroup G} (c : k) {f : (Fin n → G) → A}
    (hf : IsSlotInvariant U f) : IsSlotInvariant U (c • f) := by
  intro x s hs; simp only [Pi.smul_apply, hf x s hs]

include τ in
theorem exists_d_eq_of_res_eq_d_of_isUnit_index_three_aux
    (hidx : IsUnit ((H.index : ℕ) : k))
    (U : Subgroup G) [U.Normal] (hUH : U ≤ H)
    (u : (Fin 3 → G) → A)
    (hu : ((inhomogeneousCochains A).d 3 4).hom u = 0)
    (huU : ∀ g s : Fin 3 → G, (∀ i, s i ∈ U) → u (g * s) = u g)
    (w' : (Fin 2 → H) → A)
    (hw'U : ∀ g s : Fin 2 → H, (∀ i, (s i : G) ∈ U) → w' (g * s) = w' g)
    (hw' : ((inhomogeneousCochains (Rep.res H.subtype A)).d 2 3).hom w'
             = fun h : Fin 3 → H => u (fun i => (h i : G))) :
    ∃ w : (Fin 2 → G) → A,
      (∀ g s : Fin 2 → G, (∀ i, s i ∈ U) → w (g * s) = w g) ∧
      ((inhomogeneousCochains A).d 2 3).hom w = u := by
  obtain ⟨b, hb, hbU⟩ := exists_d_eq_corFin_resFin_sub_index_smul_three_aux A τ u hu
  obtain ⟨μ, hμ⟩ := hidx.exists_left_inv

  have hres : resFin A 3 u = ((inhomogeneousCochains (Rep.res H.subtype A)).d 2 3).hom w' := by rw [hw']; rfl
  have hcor : corFin A τ 3 (resFin A 3 u) = ((inhomogeneousCochains A).d 2 3).hom (corFin A τ 2 w') := by
    rw [hres, corFin_d_aux]
  refine ⟨μ • (corFin A τ 2 w' - b), ?_, ?_⟩
  · have h1 : IsSlotInvariant U (corFin A τ 2 w') := isSlotInvariant_corFin_aux A τ 2 U hUH w' hw'U
    exact isSlotInvariant_smul A μ (isSlotInvariant_sub A h1 (hbU U inferInstance hUH huU))
  · rw [map_smul, map_sub, hb, hcor, sub_sub_cancel, ← Nat.cast_smul_eq_nsmul k, smul_smul, hμ, one_smul]

end CorRes3

end Cores
end groupCohomology

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (N : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S)
    [K.fixingSubgroup.FiniteIndex] (hpK : ¬ p ∣ K.fixingSubgroup.index)
    (u : (Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N)
    (hlc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ i, s i ∈ F.fixingSubgroup) → u (g * s) = u g)
    (hcoc : ((inhomogeneousCochains N).d 3 4).hom u = 0)
    (w' : (Fin 2 → K.fixingSubgroup) → N)
    (hlc' : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 2 → K.fixingSubgroup,
        (∀ i, (s i : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup) → w' (g * s) = w' g)
    (hw' : ((inhomogeneousCochains (Rep.res K.fixingSubgroup.subtype N)).d 2 3).hom w'
             = fun h : Fin 3 → K.fixingSubgroup =>
                 u (fun i => (h i : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ w : (Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          (∀ i, s i ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
      ((inhomogeneousCochains N).d 2 3).hom w = u := by
  obtain ⟨F, hF, huF⟩ := hlc
  obtain ⟨F', hF', hwF'⟩ := hlc'

  obtain ⟨L, hle, hL, hLn⟩ :=
    IntermediateField.exists_normal_isUnramifiedOutside_of_le S (F ⊔ F' ⊔ K) ((hF.sup hF').sup hK)
  haveI : Normal ℚ L := hLn
  haveI : Algebra.IsSeparable ℚ L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hGL : IsGalois ℚ L := ⟨⟩
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  haveI : L.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois L).mpr hGL
  have hUK : L.fixingSubgroup ≤ K.fixingSubgroup := IntermediateField.fixingSubgroup_le (le_sup_right.trans hle)
  have hUF : L.fixingSubgroup ≤ F.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le ((le_sup_left.trans le_sup_left).trans hle)
  have hUF' : L.fixingSubgroup ≤ F'.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le ((le_sup_right.trans le_sup_left).trans hle)
  have hidx : IsUnit ((K.fixingSubgroup.index : ℕ) : ZMod p) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpK))
  obtain ⟨τ⟩ := (groupCohomology.Cores.Transversal.nonempty : Nonempty (groupCohomology.Cores.Transversal K.fixingSubgroup))
  obtain ⟨w, hwU, hdw⟩ := groupCohomology.Cores.exists_d_eq_of_res_eq_d_of_isUnit_index_three_aux N τ hidx
    L.fixingSubgroup hUK u hcoc (fun g s hs => huF g s (fun i => hUF (hs i))) w'
    (fun g s hs => hwF' g s (fun i => hUF' (hs i))) hw'
  exact ⟨w, ⟨L, hL, fun g s hs => hwU g s hs⟩, hdw⟩

end S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three
end P2MW
export P2MW.S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three (solution)
