-- Prove2me | solution 1 for mme_dwz_table2_global_common_q_aggregate_counting_capstone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T09:03:19.7364+00:00
-- url     : https://prove2.me/submissions/19e22379-b4d0-431d-b933-36f2fa1a831a

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_dwz_table2_exact_profile_coarse_Z_counts
import Theorems.Thm_mme_dwz_table2_fixed_K_target_count_factorization
import Theorems.Thm_mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
import Theorems.Thm_mme_dwz_exact_profile_useful_block_card_eq_standard
import Theorems.Thm_mme_dwz_table2_matchable_outer_family_component_words
import Theorems.Thm_mme_dwz_table2_global_canonical_bucket_supported_mix_xy_owner
import Theorems.Thm_mme_finset_enumerate_preserves_weight
import Theorems.Thm_mme_dwz_table2_reindexed_global_exact_profile_uniform_degree_base
import Theorems.Thm_mme_dwz_table2_global_exact_profile_common_prime
import Theorems.Thm_mme_dwz_global_exact_profile_conditioned_aggregate_selection
import Theorems.Thm_mme_dwz_table2_exact_profile_XYZ_marginals
import Theorems.Thm_mme_dwz_table2_reindexed_global_marginal_family_characterization
import Theorems.Thm_mme_dwz_table2_reindexed_exact_profile_subset_marginal_family
import Theorems.Thm_mme_dwz_global_exact_profile_candidate_budget_reindexed
import Theorems.Thm_mme_dwz_ambient_conditioned_fraction_le_common_state_fraction

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

/-!
# Proof body for the strengthened tensor-free counting capstone

This file is intentionally a static proof draft while the two tensor compiles
occupy the available Lean slots.  Its four formerly open interfaces now have
separate complete proof terms in neighboring files:

* `hAprofile` is coordinate-reindex transport of the three marginal counts;
* `hTsub` is exact fifteen-cell profile implies those three marginals;
* `hBudgetReindexed` is the definitional native/affine candidate-family
  identification needed to consume the common-prime budget;
* `hAmbientCommon` is the already isolated termwise ambient-to-selected-copy
  monotonicity, plus the useful-block cardinal normalization.

Everything else is the intended final proof spine and directly invokes the
public counting results.  None of these new files has been launched while the
two agreed tensor slots remain occupied.
-/

private theorem counting_capstone_at_positive_m
    (m : ℕ) (hm : 0 < m) :
    let L : ℕ := MME.DWZTable2Counts.scale * m
    let N : ℕ := L - 1
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let alphaZ : Fin 5 → ℕ := fun z ↦
      MME.DWZTable2Counts.alphaZ z * m
    let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
      ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
        MME.DWZTable2Counts.component s * m
    ∃ (n p fixedTargetCard d Q : ℕ)
        (R : ℝ) (S : Finset ℕ)
        (base : Fin L → Fin 15)
        (reindex : Fin (N + 1) ≃ Fin L)
        (q : (Fin (N + 2) → ZMod p) × ZMod p)
        (A I : Finset (Fin (N + 1) → Fin 15))
        (edge : Fin n → Fin (N + 1) → Fin 15),
      0 < m ∧
      2 ≤ p ∧
      p.Prime ∧ Odd p ∧ 4 < p ∧
      (∀ s, Fintype.card {t : Fin L // base t = s} =
        MME.DWZTable2Counts.component s * m) ∧
      fixedTargetCard = Nat.card
        {w : Fin L → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) =
            MME.DWZSquare.shapeZ (base t)) ∧
          ∀ s, Fintype.card {t : Fin L // w t = s} =
            MME.DWZTable2Counts.component s * m} ∧
      Nat.multinomial Finset.univ
            (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) =
          Nat.multinomial Finset.univ
              (fun k : Fin 5 ↦ MME.DWZTable2Counts.alphaZ k * m) *
            fixedTargetCard ∧
      0 < d ∧
      (d : ℝ) ≤
        (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 *
          (((L + 1 : ℕ) : ℝ)) ^ 15 *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              (MME.DWZSquare.maxSameMarginalEntropy -
                mme_modern_entropyBits
                  (mme_modern_marginal MME.DWZSquare.shapeX
                    MME.DWZSquare.alpha))) ∧
      R =
        (6 * (((L + 1 : ℕ) : ℝ))) ^ 9 *
          (fixedTargetCard : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP) ∧
      (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
      d ≤ 15 ^ L ∧
      Q ≤ 15 ^ L ∧
      p ≤ 2 * max 4 (8 * max d Q) ∧
      S ⊆ Finset.range (p / 2) ∧
      ThreeAPFree (S : Set ℕ) ∧
      ((p / 2 : ℕ) : ℝ) *
            Real.exp (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ)))) ≤
          (S.card : ℝ) ∧
      (∀ a, a ∈ A ↔
        (∀ x, Fintype.card
            {t : Fin (N + 1) // MME.DWZSquare.shapeX (a t) = x} =
              alphaX x) ∧
        (∀ y, Fintype.card
            {t : Fin (N + 1) // MME.DWZSquare.shapeY (a t) = y} =
              alphaY y) ∧
        ∀ z, Fintype.card
            {t : Fin (N + 1) // MME.DWZSquare.shapeZ (a t) = z} =
              alphaZ z) ∧
      I ⊆ A.filter ExactProfile ∧
      I ⊆ MME.dwzTable2AffineHashBucket S A q ∧
      (∀ e ∈ I, ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
        (fun t ↦ MME.DWZSquare.shapeX (e t)) =
            (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
          (fun t ↦ MME.DWZSquare.shapeY (e t)) =
            (fun t ↦ MME.DWZSquare.shapeY (e' t)) → e = e') ∧
      I.card = n ∧
      Function.Injective edge ∧
      Finset.univ.image edge = I ∧
      (∀ r, edge r ∈ MME.dwzTable2AffineHashBucket S A q) ∧
      (∀ r s, Fintype.card
          {t : Fin L //
            MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} =
          MME.DWZTable2Counts.component s * m) ∧
      (∀ js : Fin 3 → Fin n,
        (∀ t : Fin (N + 1),
          (MME.DWZSquare.shapeX (edge (js 0) t)).val +
            (MME.DWZSquare.shapeY (edge (js 1) t)).val +
            (MME.DWZSquare.shapeZ (edge (js 2) t)).val = 4) →
        js 0 = js 1) ∧
      ((Nat.multinomial Finset.univ
            (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) : ℝ) *
          (S.card : ℝ)) /
          (2 * (p : ℝ) ^ 2) ≤
        ∑ r, MME.DWZSquare.nonholeFraction
          (MME.DWZGlobalCorrelated.commonStateBrokenCopy
            m reindex q edge r) := by
  classical
  dsimp only
  let L : ℕ := MME.DWZTable2Counts.scale * m
  let N : ℕ := L - 1
  let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
    dsimp only [N, L]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
  let alphaX : Fin 5 → ℕ := fun x ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
      MME.DWZTable2Counts.component s.1 * m
  let alphaY : Fin 5 → ℕ := fun y ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
      MME.DWZTable2Counts.component s.1 * m
  let alphaZ : Fin 5 → ℕ := fun z ↦
    MME.DWZTable2Counts.alphaZ z * m
  let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
    ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
      MME.DWZTable2Counts.component s * m
  let T : Finset (Fin (N + 1) → Fin 15) :=
    Finset.univ.filter ExactProfile

  obtain ⟨d, A, hAmem, _hAcard, hAExactCard, hdpos,
      hxDegree, hyDegree, hdRate⟩ :=
    mme_dwz_table2_reindexed_global_exact_profile_uniform_degree_base m hm

  /- Mini-interface 1: transport the native marginal characterization of
     `A` across `reindex`.  No counting estimate is hidden here. -/
  have hAprofile : ∀ a, a ∈ A ↔
      (∀ x, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeX (a t) = x} =
            alphaX x) ∧
      (∀ y, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeY (a t) = y} =
            alphaY y) ∧
      ∀ z, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeZ (a t) = z} =
            alphaZ z := by
    simpa only [L, N, reindex, alphaX, alphaY, alphaZ] using
      mme_dwz_table2_reindexed_global_marginal_family_characterization
        m hm A hAmem

  /- Mini-interface 2: exact fifteen-cell counts imply all three marginal
     counts, hence the full exact family lies in `A`. -/
  have hTsub : T ⊆ A := by
    simpa only [T, ExactProfile] using
      mme_dwz_table2_reindexed_exact_profile_subset_marginal_family
        m N A hAprofile

  /- The degree bound itself is elementary once one exact owner is put in
     `A`: its X-fiber is a sub-finset of the full word space. -/
  have hdPow : d ≤ 15 ^ L := by
    obtain ⟨K, _hK, hOuter, _hProfiles, _hZ, _hXinj,
        _hOuterCard, _hOuterFactor⟩ :=
      mme_dwz_table2_matchable_outer_family_component_words m
    let w := Classical.choice hOuter
    let a : Fin (N + 1) → Fin 15 := fun t ↦ w.1 (reindex t)
    have haExact : ExactProfile a := by
      intro s
      exact (Fintype.card_congr
        (reindex.subtypeEquiv (fun _ ↦ Iff.rfl))).trans (w.2.2 s)
    have haT : a ∈ T := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    have haA : a ∈ A := hTsub haT
    calc
      d = (A.filter (fun b ↦
          (fun t ↦ MME.DWZSquare.shapeX (b t)) =
            (fun t ↦ MME.DWZSquare.shapeX (a t)))).card :=
        (hxDegree a haA).symm
      _ ≤ Fintype.card (Fin (N + 1) → Fin 15) := Finset.card_le_univ _
      _ = 15 ^ (N + 1) := by simp
      _ = 15 ^ L := by
        congr 1
        exact Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm)))

  obtain ⟨base, Q, p, _hCandidateCard, hQPow, _hQR, hpPrime,
      hpOdd, hp4, h8d, hCandidateBudget, _hpLower, hpUpper,
      hpReal, _hpExp⟩ :=
    mme_dwz_table2_global_exact_profile_common_prime m d hdPow
  let : Fact p.Prime := ⟨hpPrime⟩

  obtain ⟨S, hSrange, hSfree, hBehrend⟩ :=
    mme_behrend_explicit_threeAP_free (p / 2)

  let fixedTargetCard : ℕ := Nat.card
    {w : Fin L → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) =
        MME.DWZSquare.shapeZ (base.1 t)) ∧
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m}
  let R : ℝ :=
    (6 * (((L + 1 : ℕ) : ℝ))) ^ 9 *
      (fixedTargetCard : ℝ) *
      Real.exp
        ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          MME.DWZSquare.logAlphaP)
  have hBaseZ := mme_dwz_table2_exact_profile_coarse_Z_counts
    m base.1 base.2
  have hFactor := mme_dwz_table2_fixed_K_target_count_factorization
    m (fun t ↦ MME.DWZSquare.shapeZ (base.1 t)) hBaseZ

  let cap : ℕ := Fintype.card
    (MME.DWZComponentRestriction.DWZStandardBlock m)
  have hcapPos : 0 < cap := by
    have hsmall := mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
      m base.1 base.2
    have hcard := mme_dwz_exact_profile_useful_block_card_eq_standard
      m base.1 base.2
    change 0 < Fintype.card
      (MME.DWZComponentRestriction.DWZStandardBlock m)
    rw [← hcard]
    exact Fintype.card_pos_iff.mpr hsmall
  have hcapEq : ∀ a, a ∈ T →
      Fintype.card (MME.DWZTable2StandardForm.UsefulBlock m
        (fun t ↦ a (reindex.symm t))) = cap := by
    intro a ha
    apply mme_dwz_exact_profile_useful_block_card_eq_standard
    intro s
    let E : {t : Fin L // a (reindex.symm t) = s} ≃
        {t : Fin (N + 1) // a t = s} :=
      reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl)
    exact (Fintype.card_congr E).trans ((Finset.mem_filter.mp ha).2 s)

  /- Mini-interface 3: the common-prime theorem phrases candidates in native
     source order; the selector phrases the same filtered family after
     `reindex`.  This is only `Finset.filter` extensionality plus the native
     exact-profile proof. -/
  have hBudgetReindexed :
      let native : (Fin (N + 1) → Fin 15) → Fin L → Fin 15 :=
        fun a t ↦ a (reindex.symm t)
      let Tnative : Finset (Fin L → Fin 15) :=
        Finset.univ.filter fun w : Fin L → Fin 15 ↦
          ∀ s, Fintype.card {t : Fin L // w t = s} =
            MME.DWZTable2Counts.component s * m
      let grade : ∀ a,
          MME.DWZTable2StandardForm.UsefulBlock m (native a) →
            Fin L → Fin (3 * 3) := fun _ z t ↦
        MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
      ∀ a, a ∈ T → ∀ z,
        8 * (Tnative.filter (fun w : Fin L → Fin 15 ↦
          (∀ t, MME.DWZSquare.shapeZ (w t) =
            MME.DWZSquare.shapeZ (native a t)) ∧
          MME.DWZStep2Source.retainedFineCompatible m
            (fun w : Fin L → Fin 15 ↦ w) (grade a z) w)).card ≤ p := by
    simpa only [L, N, reindex, ExactProfile, T] using
      (mme_dwz_global_exact_profile_candidate_budget_reindexed
        m hm (p := p) hCandidateBudget)

  obtain ⟨q, I, hIT, hIBucket, hIsolated, hSelectedMass⟩ :=
    mme_dwz_global_exact_profile_conditioned_aggregate_selection
      m hm hpOdd hp4 S hSrange hSfree A d cap hcapPos h8d
        hTsub
        (fun a ha ↦ (hxDegree a (hTsub ha)).le)
        (fun a ha ↦ (hyDegree a (hTsub ha)).le)
        (by simpa only [L, N, reindex, ExactProfile, T] using
          hBudgetReindexed)
        (by simpa only [L, N, reindex, ExactProfile, T, cap] using hcapEq)

  let native : (Fin (N + 1) → Fin 15) → Fin L → Fin 15 :=
    fun a t ↦ a (reindex.symm t)
  let Tnative : Finset (Fin L → Fin 15) :=
    Finset.univ.filter fun w : Fin L → Fin 15 ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
  let mass : (Fin (N + 1) → Fin 15) → ℝ := fun a ↦
    (((if ha : a ∈ T then
        (MME.DWZGlobalCorrelated.ambientConditionedBrokenCopy
          m reindex Tnative (native a) (by
            simp only [Tnative, Finset.mem_filter, Finset.mem_univ, true_and]
            intro s
            let E : {t : Fin L // native a t = s} ≃
                {t : Fin (N + 1) // a t = s} :=
              reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl)
            exact (Fintype.card_congr E).trans
              ((Finset.mem_filter.mp ha).2 s))
            (fun t ↦ q.1 t.castSucc)).nonholes.card
      else 0) : ℕ) : ℝ) / (cap : ℝ)

  obtain ⟨edge, hedgeInjective, hedgeI, hedgeSurjective, hMassEnum⟩ :=
    mme_finset_enumerate_preserves_weight I mass
  have hImage : Finset.univ.image edge = I := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨r, _hr, rfl⟩
      exact hedgeI r
    · intro ha
      obtain ⟨r, hr⟩ := hedgeSurjective a ha
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr⟩
  have hedgeBucket : ∀ r,
      edge r ∈ MME.dwzTable2AffineHashBucket S A q :=
    fun r ↦ hIBucket (hedgeI r)
  have hedgeExact : ∀ r, ExactProfile (edge r) := fun r ↦
    (Finset.mem_filter.mp (hIT (hedgeI r))).2
  have hedgeProfile : ∀ r s,
      Fintype.card
          {t : Fin L //
            MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} =
        MME.DWZTable2Counts.component s * m := by
    intro r s
    let E : {t : Fin L //
        MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} ≃
        {t : Fin (N + 1) // edge r t = s} :=
      reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl)
    exact (Fintype.card_congr E).trans (hedgeExact r s)
  have hXYOwner : ∀ js : Fin 3 → Fin I.card,
      (∀ t : Fin (N + 1),
        (MME.DWZSquare.shapeX (edge (js 0) t)).val +
          (MME.DWZSquare.shapeY (edge (js 1) t)).val +
          (MME.DWZSquare.shapeZ (edge (js 2) t)).val = 4) →
      js 0 = js 1 := by
    intro js hs
    exact mme_dwz_table2_global_canonical_bucket_supported_mix_xy_owner
      S A I q alphaX alphaY alphaZ hAprofile edge hedgeInjective
        hedgeI hIBucket hIsolated js hs

  /- Mini-interface 4: for every enumerated owner, bucket membership gives
     affine retention at `q`; the proved ambient-to-commonState monotonicity
     theorem then compares nonhole cardinals termwise, and `hcapEq` rewrites
     the denominator to `cap`. -/
  have hAmbientCommon : ∀ r,
      mass (edge r) ≤ MME.DWZSquare.nonholeFraction
        (MME.DWZGlobalCorrelated.commonStateBrokenCopy
          m reindex q edge r) := by
    intro r
    have hrT : edge r ∈ T := hIT (hedgeI r)
    have hedgeTnative : ∀ j,
        MME.DWZGlobalCorrelated.sourceWord reindex edge j ∈ Tnative := by
      intro j
      simp only [Tnative, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hedgeProfile j
    have hfrac :=
      mme_dwz_ambient_conditioned_fraction_le_common_state_fraction
        m hpOdd reindex S hSrange hSfree A Tnative q edge
          hedgeTnative hedgeInjective r (hedgeBucket r)
    have hcapEdge : Fintype.card
        (MME.DWZTable2StandardForm.UsefulBlock m
          (MME.DWZGlobalCorrelated.sourceWord reindex edge r)) = cap :=
      hcapEq (edge r) hrT
    dsimp only at hfrac
    rw [hcapEdge] at hfrac
    refine le_trans (le_of_eq ?_) hfrac
    simp only [mass, dif_pos hrT, native, Tnative]
    all_goals rfl
  have hSelectedMassNormalized :
      ((T.card : ℝ) * (S.card : ℝ)) /
          (2 * (p : ℝ) ^ 2) ≤ ∑ a ∈ I, mass a := by
    simpa only [L, N, reindex, ExactProfile, T, native, Tnative,
      mass, cap] using hSelectedMass
  have hFinalMass :
      ((Nat.multinomial Finset.univ
            (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) : ℝ) *
          (S.card : ℝ)) /
          (2 * (p : ℝ) ^ 2) ≤
        ∑ r, MME.DWZSquare.nonholeFraction
          (MME.DWZGlobalCorrelated.commonStateBrokenCopy
            m reindex q edge r) := by
    calc
      ((Nat.multinomial Finset.univ
              (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) : ℝ) *
            (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) =
          ((T.card : ℝ) * (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) := by
          congr 3
          have hfilter : A.filter ExactProfile = T := by
            ext a
            simp only [Finset.mem_filter, T, Finset.mem_univ, true_and]
            constructor
            · exact fun ha ↦ ha.2
            · intro ha
              exact ⟨hTsub (by
                simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and]
                  using ha), ha⟩
          rw [← hfilter, hAExactCard]
      _ ≤ ∑ a ∈ I, mass a := by
        exact hSelectedMassNormalized
      _ = ∑ r, mass (edge r) := hMassEnum.symm
      _ ≤ ∑ r, MME.DWZSquare.nonholeFraction
          (MME.DWZGlobalCorrelated.commonStateBrokenCopy
            m reindex q edge r) := Finset.sum_le_sum fun r _ ↦ hAmbientCommon r

  refine ⟨I.card, p, fixedTargetCard, d, Q, R, S, base.1,
    reindex, q, A, I, edge, hm, ?_, hpPrime, hpOdd, hp4, base.2,
    rfl, ?_, hdpos, hdRate, rfl, ?_, hdPow, hQPow, hpUpper,
    hSrange, hSfree, hBehrend, hAprofile, ?_, hIBucket,
    hIsolated, rfl, hedgeInjective, hImage, hedgeBucket,
    hedgeProfile, hXYOwner, hFinalMass⟩
  · omega
  · simpa only [fixedTargetCard] using hFactor
  · simpa only [R, fixedTargetCard, L] using hpReal
  · intro a ha
    exact Finset.mem_filter.mpr
      ⟨hTsub (hIT ha), (Finset.mem_filter.mp (hIT ha)).2⟩

theorem solution :
    ∀ᶠ m : ℕ in atTop,
      let L : ℕ := MME.DWZTable2Counts.scale * m
      let N : ℕ := L - 1
      let alphaX : Fin 5 → ℕ := fun x ↦
        ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
          MME.DWZTable2Counts.component s.1 * m
      let alphaY : Fin 5 → ℕ := fun y ↦
        ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
          MME.DWZTable2Counts.component s.1 * m
      let alphaZ : Fin 5 → ℕ := fun z ↦
        MME.DWZTable2Counts.alphaZ z * m
      let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
        ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
          MME.DWZTable2Counts.component s * m
      ∃ (n p fixedTargetCard d Q : ℕ)
          (R : ℝ) (S : Finset ℕ)
          (base : Fin L → Fin 15)
          (reindex : Fin (N + 1) ≃ Fin L)
          (q : (Fin (N + 2) → ZMod p) × ZMod p)
          (A I : Finset (Fin (N + 1) → Fin 15))
          (edge : Fin n → Fin (N + 1) → Fin 15),
        0 < m ∧
        2 ≤ p ∧
        p.Prime ∧ Odd p ∧ 4 < p ∧
        (∀ s,
          Fintype.card {t : Fin L // base t = s} =
            MME.DWZTable2Counts.component s * m) ∧
        fixedTargetCard = Nat.card
          {w : Fin L → Fin 15 //
            (∀ t, MME.DWZSquare.shapeZ (w t) =
              MME.DWZSquare.shapeZ (base t)) ∧
            ∀ s, Fintype.card {t : Fin L // w t = s} =
              MME.DWZTable2Counts.component s * m} ∧
        Nat.multinomial Finset.univ
              (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) =
            Nat.multinomial Finset.univ
                (fun k : Fin 5 ↦ MME.DWZTable2Counts.alphaZ k * m) *
              fixedTargetCard ∧
        0 < d ∧
        (d : ℝ) ≤
          (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 *
            (((L + 1 : ℕ) : ℝ)) ^ 15 *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                (MME.DWZSquare.maxSameMarginalEntropy -
                  mme_modern_entropyBits
                    (mme_modern_marginal MME.DWZSquare.shapeX
                      MME.DWZSquare.alpha))) ∧
        R =
          (6 * (((L + 1 : ℕ) : ℝ))) ^ 9 *
            (fixedTargetCard : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP) ∧
        (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
        d ≤ 15 ^ L ∧
        Q ≤ 15 ^ L ∧
        p ≤ 2 * max 4 (8 * max d Q) ∧
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        ((p / 2 : ℕ) : ℝ) *
              Real.exp (-4 * Real.sqrt
                (Real.log (((p / 2 : ℕ) : ℝ)))) ≤
            (S.card : ℝ) ∧
        (∀ a, a ∈ A ↔
          (∀ x, Fintype.card
              {t : Fin (N + 1) //
                MME.DWZSquare.shapeX (a t) = x} = alphaX x) ∧
          (∀ y, Fintype.card
              {t : Fin (N + 1) //
                MME.DWZSquare.shapeY (a t) = y} = alphaY y) ∧
          ∀ z, Fintype.card
              {t : Fin (N + 1) //
                MME.DWZSquare.shapeZ (a t) = z} = alphaZ z) ∧
        I ⊆ A.filter ExactProfile ∧
        I ⊆ MME.dwzTable2AffineHashBucket S A q ∧
        (∀ e ∈ I,
          ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
            (fun t ↦ MME.DWZSquare.shapeX (e t)) =
                (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
              (fun t ↦ MME.DWZSquare.shapeY (e t)) =
                (fun t ↦ MME.DWZSquare.shapeY (e' t)) →
            e = e') ∧
        I.card = n ∧
        Function.Injective edge ∧
        Finset.univ.image edge = I ∧
        (∀ r, edge r ∈ MME.dwzTable2AffineHashBucket S A q) ∧
        (∀ r s,
          Fintype.card
              {t : Fin L //
                MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} =
            MME.DWZTable2Counts.component s * m) ∧
        (∀ js : Fin 3 → Fin n,
          (∀ t : Fin (N + 1),
            (MME.DWZSquare.shapeX (edge (js 0) t)).val +
              (MME.DWZSquare.shapeY (edge (js 1) t)).val +
              (MME.DWZSquare.shapeZ (edge (js 2) t)).val = 4) →
          js 0 = js 1) ∧
        ((Nat.multinomial Finset.univ
              (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) : ℝ) *
            (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤
          ∑ r, MME.DWZSquare.nonholeFraction
            (MME.DWZGlobalCorrelated.commonStateBrokenCopy
              m reindex q edge r) := by
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact counting_capstone_at_positive_m m hm
