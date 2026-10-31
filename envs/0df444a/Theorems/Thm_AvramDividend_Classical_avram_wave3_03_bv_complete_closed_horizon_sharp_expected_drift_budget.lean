-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:43:14.61421+00:00
-- url     : https://prove2.me/theorems/23ddd713-8f78-4c6f-b478-98e0a5b32c7c
-- title:
--   Sharp unconditional source BV complete closed-horizon dividend expectation budget
-- statement:
--   For every actual standing bounded-variation spectrally negative Levy process, nonnegative initial reserve, admissible finite-cap dividend strategy, nonnegative discount and terminal time T, the entire original discounted dividend Stieltjes reward over [0,T], integrated over all ruin paths, is at most initial reserve plus exactly T times physical drift. This accounts for initial and terminal atoms and any continuous dividend component, with no auxiliary later-horizon slack.
-- source:
--   Unconditional original source BV complete closed-horizon expectation bound at every H>T, standing BV nonnegative drift, and proved extended nonnegative order-limit theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_expected_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_ennreal_drift_budget_strict_horizon_to_closed

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (x + (T : ℝ) * X.drift) := by sorry
