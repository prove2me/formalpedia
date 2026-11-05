-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_rightcont_l2_martingale_of_cauchy
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_rightcont_l2_martingale_of_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:06:12.77722+00:00
-- url     : https://prove2.me/theorems/2f7912f8-e97d-4531-8391-4032ff1ac4be
-- title:
--   Original-process right-continuous finite-band L2 martingale completion from a Cauchy family
-- statement:
--   On the exact original Avram probability space P and right-continuous filtration, a Cauchy sequence of source finite-band L2 martingales determines an L2 limit process, which is adapted and retains the martingale conditional expectation identities. This removes the separately supplied limit and convergence hypotheses of the Proved original L2 closure theorem. The original-source Cauchy, adaptedness and conditional-centering hypotheses remain genuine obligations.
-- source:
--   Deduce the pointwise-in-time Lp completion from Mathlib cauchySeq_tendsto_of_complete, then apply Proved original right-continuous L2 martingale closure 0fc9c4fb-2505-4402-80dc-02405da8f273. The construction never uses the LeanLevy synthetic Poisson point family.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightcont_l2_band_martingale_limit
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_rightcont_l2_martingale_of_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (hCauchy : ∀ t, CauchySeq (fun n => M n t))
    (hAdapt : ∀ s n,
      ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (M n s) :
        Lp ℝ (2 : ℝ≥0∞) P) = M n s)
    (hCenter : ∀ s t, s ≤ t → ∀ n,
      (MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (M n t - M n s) = 0) :
    ∃ L : ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P,
      (∀ t, Tendsto (fun n => M n t) atTop (𝓝 (L t))) ∧
      (∀ s, ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (L s) :
        Lp ℝ (2 : ℝ≥0∞) P) = L s) ∧
      (∀ s t, s ≤ t →
        ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (L t) :
          Lp ℝ (2 : ℝ≥0∞) P) = L s) := by sorry
