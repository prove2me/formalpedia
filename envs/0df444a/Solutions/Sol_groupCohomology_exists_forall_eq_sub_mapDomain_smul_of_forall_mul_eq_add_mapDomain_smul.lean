-- Prove2me | solution 1 for groupCohomology.exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/34b0762d-edd4-5d87-b024-b8f6b9f6e03d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul

set_option autoImplicit false

theorem solution
    {G : Type} [Group G] [Finite G] {X : Type} [MulAction G X]
    (n : G → X →₀ ℤ) (hn : ∀ g h : G, n (g * h) = n g + Finsupp.mapDomain (g • ·) (n h)) :
    ∃ m : X →₀ ℤ, ∀ g : G, n g = m - Finsupp.mapDomain (g • ·) m := by
  classical
  haveI : Fintype G := Fintype.ofFinite G

  have hmd : ∀ (g : G) (φ : X →₀ ℤ) (x : X), Finsupp.mapDomain (g • ·) φ x = φ (g⁻¹ • x) := fun g φ x => by
    conv_lhs => rw [← smul_inv_smul g x]
    exact Finsupp.mapDomain_apply (MulAction.injective g) φ (g⁻¹ • x)

  have hn1 : n 1 = 0 := by
    have := hn 1 1
    rw [one_mul] at this
    have h2 : Finsupp.mapDomain ((1 : G) • ·) (n 1) = n 1 := by
      simp only [one_smul]; exact Finsupp.mapDomain_id
    rw [h2] at this
    simpa using this

  have hstab : ∀ (x₀ : X) (h : G), h • x₀ = x₀ → n h x₀ = 0 := by
    intro x₀ h hh
    have hfix : ∀ k : ℕ, h ^ k • x₀ = x₀ := by
      intro k
      induction k with
      | zero => rw [pow_zero, one_smul]
      | succ k ih => rw [pow_succ, mul_smul, hh, ih]

    have hpow : ∀ k : ℕ, n (h ^ k) x₀ = k * n h x₀ := by
      intro k
      induction k with
      | zero => simp [hn1]
      | succ k ih =>
        rw [pow_succ, hn, Finsupp.add_apply, hmd, ih, inv_smul_eq_iff.2 (hfix k).symm]
        push_cast
        ring
    have hord := hpow (orderOf h)
    rw [pow_orderOf_eq_one, hn1, Finsupp.zero_apply] at hord
    have hpos : (0 : ℤ) < orderOf h := by exact_mod_cast orderOf_pos h
    rcases mul_eq_zero.1 hord.symm with h0 | h0
    · exact absurd h0 (ne_of_gt hpos)
    · exact h0

  let rep : X → X := fun x => (Quotient.mk (MulAction.orbitRel G X) x).out
  have hrep : ∀ x, ∃ t : G, t • rep x = x := fun x => by
    have : rep x ∈ MulAction.orbit G x := Quotient.mk_out (s := MulAction.orbitRel G X) x
    obtain ⟨g, hg⟩ := this
    exact ⟨g⁻¹, by rw [← hg]; simp⟩
  have hrep_smul : ∀ (g : G) (x : X), rep (g • x) = rep x := fun g x => by
    show (Quotient.mk (MulAction.orbitRel G X) (g • x)).out = (Quotient.mk (MulAction.orbitRel G X) x).out
    congr 1
    exact Quotient.sound ⟨g, rfl⟩
  choose t ht using hrep

  have hwd : ∀ (x : X) (s : G), s • rep x = x → n s x = n (t x) x := by
    intro x s hs
    have hst : ((t x)⁻¹ * s) • rep x = rep x := by rw [mul_smul, hs, inv_smul_eq_iff, ht x]
    have : s = t x * ((t x)⁻¹ * s) := by group
    rw [this, hn, Finsupp.add_apply, hmd]
    have hx : (t x)⁻¹ • x = rep x := by rw [inv_smul_eq_iff, ht x]
    rw [hx, hstab (rep x) _ hst, add_zero]

  let mf : X → ℤ := fun x => n (t x) x
  have hmf_supp : ∀ x, mf x ≠ 0 → x ∈ Finset.univ.biUnion fun s : G => (n s).support := fun x hx => by
    rw [Finset.mem_biUnion]
    exact ⟨t x, Finset.mem_univ _, Finsupp.mem_support_iff.2 hx⟩
  let m : X →₀ ℤ := Finsupp.onFinset (Finset.univ.biUnion fun s : G => (n s).support) mf hmf_supp
  have hm : ∀ x, m x = n (t x) x := fun x => rfl
  refine ⟨m, fun g => Finsupp.ext fun x => ?_⟩
  rw [Finsupp.sub_apply, hmd, hm, hm]

  have hdec : n (t x) x = n g x + n (g⁻¹ * t x) (g⁻¹ • x) := by
    conv_lhs => rw [show t x = g * (g⁻¹ * t x) by group, hn]
    rw [Finsupp.add_apply, hmd]
  have htr : (g⁻¹ * t x) • rep (g⁻¹ • x) = g⁻¹ • x := by rw [hrep_smul, mul_smul, ht x]
  rw [hdec, hwd (g⁻¹ • x) _ htr]
  ring

end S_groupCohomology_exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul
end P2MW
export P2MW.S_groupCohomology_exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul (solution)
