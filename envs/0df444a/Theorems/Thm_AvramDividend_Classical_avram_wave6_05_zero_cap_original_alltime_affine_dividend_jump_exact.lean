-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_zero_cap_original_alltime_affine_dividend_jump_exact
-- name    : AvramDividend.Classical.avram_wave6_05_zero_cap_original_alltime_affine_dividend_jump_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:01:59.003209+00:00
-- url     : https://prove2.me/theorems/d87e8d35-7ce5-469b-b4ec-f319104e8ee0
-- title:
--   Literal zero-cap original admissible right dividend atom equals exact cap-linear value loss at every permitted time
-- statement:
--   At literal dividend cap zero, the cap-linear verification extension is affine of slope one on nonnegative reserves. Every admissible chronological right-payment atom, at time zero or strictly before ruin and after any original Lévy source jump, has exactly the same V value drop as cash paid. Admissibility supplies postpayment solvency 0≤U−δ and nondecreasing D supplies δ≥0; hence both endpoints are nonnegative and the cap-linear extension has the identity V(U)−V(U−δ)=δ. The theorem handles literal zero cap distinctly from positive-cap gradient hypotheses and does not impose a finite-jump control assumption.
-- source:
--   Canonical IsAdmissibleLe, dividendStrategy_le_rightLimit and literal C=0 cap-linear V definition. No derivative regularity is needed at the empty interior of the zero cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_zero_cap_original_alltime_affine_dividend_jump_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (w V : ℝ → ℝ)
    (hVzero : ∀ y : ℝ,
      V y = if y ≤ 0 then w y else w 0 + y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (0 : ℝ≥0∞) D)
    (ω : Ω) (t : ℝ≥0)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω =
      V (riskProcess X x D t ω) -
        V (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) := by sorry
