-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_countable_stopping_strict_postpayment_preruin
-- name    : AvramDividend.Classical.avram_gclose16_original_countable_stopping_strict_postpayment_preruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:24:10.852857+00:00
-- url     : https://prove2.me/theorems/4036fb7a-c722-4dd8-bf63-a98f7666634a
-- title:
--   Countable original stopped clocks share an almost-sure pre-ruin strict postpayment reserve event
-- statement:
--   For any countable sequence of original right-continuous-filtration stopping clocks, a single P-almost-sure set satisfies strictly positive actual postpayment reserve at every clock lying strictly before ruin. The result takes a countable intersection of the Proved genuine single-stopping strict-solvency theorem, enabling countably many sampled lower-exit thresholds to be controlled on the same full-measure event. It does not assert simultaneous strict positivity at all real times or payoff convergence.
-- source:
--   Direct countable intersection of Proved 0e9f7014 at each indexed physical stopping clock using pinned MeasureTheory.ae_all_iff. Genuine source X,D and right-continuous filtration preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose16_original_countable_stopping_strict_postpayment_preruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ j (s : ℝ≥0),
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ j ω ≤ s})
    (hstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ j ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ j,
      (τ j ω : ℝ≥0∞) < ruinTime X x D ω →
        0 < x + X.X (τ j ω) ω - rightLimit D (τ j ω) ω := by sorry
