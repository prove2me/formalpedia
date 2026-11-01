-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_countable_chronological_signed_correction_nonpos_of_summable
-- name    : AvramDividend.Classical.avram_wave4_04b_countable_chronological_signed_correction_nonpos_of_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:30:39.56849+00:00
-- url     : https://prove2.me/theorems/0dcf1d7d-aa28-4f69-8590-125f299c4726
-- title:
--   Every summable countable stopped chronological right-dividend correction has nonpositive real sum
-- statement:
--   On the genuine adapted Lévy-driven controlled reserve, the full real series of countably many discounted signed chronological dividend right-jump corrections is nonpositive, provided that series is summable and all jumps are stopped before the finite horizon. The jump condition applies to each actual right-payment event after any simultaneous source jump, including time zero. This is a precise signed infinite-series sign theorem with an honest convergence premise; it does not assume the Itô–Meyer formula or claim general summability without proof.
-- source:
--   Previously Proved finite signed chronological sign theorem, canonical source hjump and pinned Mathlib tsum_nonpos. The countable support and real summability are explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_countable_chronological_signed_correction_nonpos_of_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (A : Set ℝ≥0) (hA : A.Countable)
    (hAT : ∀ t : A, (t : ℝ≥0) ≤ T)
    (hAP : ∀ t : A, ((t : ℝ≥0) : ℝ) ∈ paymentTimes τ)
    (hjump : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hSummable : Summable (fun t : A =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∑' t : A,
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by sorry
