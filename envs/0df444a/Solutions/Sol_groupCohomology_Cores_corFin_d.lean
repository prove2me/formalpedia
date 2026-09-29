-- Prove2me | solution 1 for groupCohomology.Cores.corFin_d
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9b990f7c-7630-5557-b987-86bd40bda45e

import Mathlib
import Definitions.Def_GroupCohomology_CorestrictionFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Cores_corFin_d

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_Cores_corFin_d.groupCohomology groupCohomology.Cores P2MW.S_groupCohomology_Cores_corFin_d.groupCohomology.Cores"

namespace groupCohomology
p2m_export "groupCohomology" "congr map inhomogeneousCochains.d_def inhomogeneousCochains"
p2m_open "groupCohomology"
namespace Cores
p2m_export "groupCohomology.Cores" "IsSlotInvariant corFin Transversal Transversal.qinv fintypeQuot"
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

theorem solution
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex]
    (τ : Transversal H) (n : ℕ) (u : (Fin n → H) → A) :
    corFin A τ (n + 1) (((inhomogeneousCochains (Rep.res H.subtype A)).d n (n + 1)).hom u)
      = ((inhomogeneousCochains A).d n (n + 1)).hom (corFin A τ n u) :=
  groupCohomology.Cores.corFin_d_aux A τ n u

end S_groupCohomology_Cores_corFin_d
end P2MW
export P2MW.S_groupCohomology_Cores_corFin_d (solution)
