-- Prove2me | solution 1 for groupCohomology.finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f3ebe878-5b8e-5c9a-ae3f-c5a6c789a6f3

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Definitions.Def_GroupCohomology_TateTwist
import Theorems.Thm_groupCohomology_exists_cocycles1_apply_eq_of_frobenius_tame_relations
import Theorems.Thm_groupCohomology_finiteDimensional_H1_of_finite
import Theorems.Thm_groupCohomology_finrank_H1_eq_finrank_inflationImage_add_finrank_range_res
import Theorems.Thm_groupCohomology_finrank_range_res_eq_finrank_range_evalAtGen
import Theorems.Thm_groupCohomology_finrank_inflationImage_eq_finrank_invariants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [Field k] [Group G] [Finite G] (A : Rep k G) [FiniteDimensional k A]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)] (t : G) (ht : t ∈ S) (htS : S ≤ Subgroup.zpowers t)
    (φ : G) (hφ : ∀ x : G ⧸ S, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : G ⧸ S))
    (m : ℕ) (hm : φ⁻¹ * t * φ = t ^ m) (hst : φ * t * φ⁻¹ ∈ Subgroup.zpowers t)
    (j : ℕ) (hrel : φ ^ orderOf (QuotientGroup.mk φ : G ⧸ S) = t ^ j)

    (hNt : ∑ i ∈ Finset.range (orderOf t), A.ρ (t ^ i) = 0)
    (hNj : ∑ i ∈ Finset.range j, A.ρ (t ^ i) = 0)
    (hNφ : ∑ i ∈ Finset.range (orderOf (QuotientGroup.mk φ : G ⧸ S)), A.ρ (φ ^ i) = 0)
    (hN : (A.quotientToInvariants S).ρ.norm = 0) :
    finrank k A.ρ.invariants
        + finrank k (LinearMap.ker (m • frobeniusOnCoinvariants A t φ hst - 1))
      ≤ finrank k (H1 A) := by
  classical
  haveI : FiniteDimensional k (H1 A) := finiteDimensional_H1_of_finite A
  have h1 := finrank_H1_eq_finrank_inflationImage_add_finrank_range_res A S
  have h2 := finrank_inflationImage_eq_finrank_invariants A S hφ hN
  have h3 := finrank_range_res_eq_finrank_range_evalAtGen A S t ht htS
  have hzp : Subgroup.zpowers t ≤ S := (Subgroup.zpowers_le).2 ht
  have hgen : ∀ x : G, ∃ a b : ℕ, x = φ ^ a * t ^ b := by
    intro x
    obtain ⟨a, ha⟩ := (mem_powers_iff_mem_zpowers).2 (hφ (QuotientGroup.mk x))
    have hs : (φ ^ a)⁻¹ * x ∈ S := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_pow]
      exact ha
    obtain ⟨b, hb⟩ := (mem_powers_iff_mem_zpowers).2 (htS hs)
    change t ^ b = _ at hb
    exact ⟨a, b, by rw [hb]; group⟩
  have hmin : ∀ d : ℕ, φ ^ d ∈ Subgroup.zpowers t → orderOf (QuotientGroup.mk φ : G ⧸ S) ∣ d := by
    intro d hd
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hzp hd
  let R : Submodule k A := LinearMap.range (A.ρ t - 1)
  have hpow : ∀ (a : ℕ) (z : A), A.ρ (t ^ a) z - z ∈ R := by
    intro a z
    induction a with
    | zero => rw [pow_zero, map_one, Module.End.one_apply, sub_self]; exact Submodule.zero_mem _
    | succ a ih =>
      have : A.ρ (t ^ (a + 1)) z - z = (A.ρ t - 1) (A.ρ (t ^ a) z) + (A.ρ (t ^ a) z - z) := by
        rw [pow_succ', map_mul, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
        abel
      rw [this]
      exact R.add_mem ⟨_, rfl⟩ ih
  have hRφ : ∀ z ∈ R, A.ρ φ z ∈ R := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨c, hc⟩ := (mem_powers_iff_mem_zpowers).2 hst
    change t ^ c = _ at hc
    have hφt : φ * t = t ^ c * φ := by rw [hc]; group
    have : A.ρ φ ((A.ρ t - 1) y) = A.ρ (t ^ c) (A.ρ φ y) - A.ρ φ y := by
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, ← Module.End.mul_apply, ← map_mul, hφt,
        map_mul, Module.End.mul_apply]
    rw [this]
    exact hpow c _
  have hsub : LinearMap.ker (m • frobeniusOnCoinvariants A t φ hst - 1) ≤ LinearMap.range (evalAtGen A t) := by
    intro x hx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      ← Nat.cast_smul_eq_nsmul k, LinearMap.smul_apply, frobeniusOnCoinvariants_mk,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hx

    have hNm : (∑ i ∈ Finset.range m, A.ρ (t ^ i) v) - (m : k) • v ∈ R := by
      have : (∑ i ∈ Finset.range m, A.ρ (t ^ i) v) - (m : k) • v = ∑ i ∈ Finset.range m, (A.ρ (t ^ i) v - v) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul k]
      rw [this]
      exact R.sum_mem fun i _ => hpow i v
    have hwR : A.ρ φ (∑ i ∈ Finset.range m, A.ρ (t ^ i) v) - v ∈ R := by
      have : A.ρ φ (∑ i ∈ Finset.range m, A.ρ (t ^ i) v) - v
          = A.ρ φ ((∑ i ∈ Finset.range m, A.ρ (t ^ i) v) - (m : k) • v) + ((m : k) • A.ρ φ v - v) := by
        rw [map_sub, map_smul]; abel
      rw [this]
      exact R.add_mem (hRφ _ hNm) hx
    obtain ⟨w, hw⟩ := hwR
    obtain ⟨c, hc⟩ := groupCohomology.exists_cocycles1_apply_eq_of_frobenius_tame_relations A t φ m
      (orderOf (QuotientGroup.mk φ : G ⧸ S)) j hm hrel hmin hgen hNφ v w
      (by rw [← LinearMap.sum_apply, hNt, LinearMap.zero_apply])
      (by rw [← LinearMap.sum_apply, hNj, LinearMap.zero_apply])
      (by rw [← hw, LinearMap.sub_apply, Module.End.one_apply])
    exact ⟨c, by rw [evalAtGen_apply, hc]⟩
  have h4 : finrank k (LinearMap.ker (m • frobeniusOnCoinvariants A t φ hst - 1))
      ≤ finrank k (LinearMap.range (evalAtGen A t)) := Submodule.finrank_mono hsub
  omega

end S_groupCohomology_finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth
end P2MW
export P2MW.S_groupCohomology_finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth (solution)
