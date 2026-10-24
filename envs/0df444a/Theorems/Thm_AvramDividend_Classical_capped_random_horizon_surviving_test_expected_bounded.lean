-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_random_horizon_surviving_test_expected_bounded
-- name    : AvramDividend.Classical.capped_random_horizon_surviving_test_expected_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:53:27.130361+00:00
-- url     : https://prove2.me/theorems/a53adcc1-e69c-4304-983c-4ecd6bf9f85d
-- title:
--   Uniform expected absolute HJB terminal bound at arbitrary random localisation times under a finite reserve cap
-- statement:
--   If the capped admissible controlled reserve starts in [0,B], then at every random time preceding ruin its value remains in [0,B]. A continuous HJB verification function is uniformly bounded in absolute value on that interval. Thus the nonnegative expected absolute value of the stopped terminal test payoff is bounded by a finite constant, including the time-zero case and without an optional-stopping assumption on the random time. This supplies a domination/integrability ingredient for both BV and UV stochastic verification.
-- source:
--   Two canonically proved finite-cap and pathwise reserve lemmas, Mathlib real compactness and lintegral_mono.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_random_horizon_surviving_test_expected_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∫⁻ ω, if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        ENNReal.ofReal (|w (riskProcess X x D (τ ω) ω)|) else 0 ∂P) ≤
      ENNReal.ofReal M := by sorry
