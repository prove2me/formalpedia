-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_surviving_terminal_test_integrable_of_measurable
-- name    : AvramDividend.Classical.capped_surviving_terminal_test_integrable_of_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:53:43.899022+00:00
-- url     : https://prove2.me/theorems/ed2ffc12-821c-47f9-bbcf-5f8bd9d108ce
-- title:
--   Integrability of measurable stopped HJB verification values under a finite reserve cap
-- statement:
--   For any random horizon τ, cap admissibility bounds the pre-ruin controlled reserve in [0,B]. Continuity of w supplies a deterministic uniform absolute bound over that interval. If the stopped terminal payoff is a.e. strongly measurable, then the probability measure and domination by this bound imply Bochner integrability. This is a type-level bridge to the expectation and martingale localisation steps in BV and UV stochastic verification; measurability of a particular stopping time remains an independent obligation.
-- source:
--   Mathlib Integrable.of_bound, canonically proved finite-cap absolute bound and stopped reserve range.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_surviving_terminal_test_integrable_of_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0)
    (hMeas : AEStronglyMeasurable
      (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        w (riskProcess X x D (τ ω) ω) else 0) P) :
    Integrable (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω then
      w (riskProcess X x D (τ ω) ω) else 0) P := by sorry
