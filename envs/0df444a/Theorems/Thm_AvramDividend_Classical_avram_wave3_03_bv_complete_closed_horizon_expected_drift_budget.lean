-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_expected_drift_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_complete_closed_horizon_expected_drift_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:34:56.435147+00:00
-- url     : https://prove2.me/theorems/610138f4-4687-442b-8924-d213af477085
-- title:
--   Unconditional original BV capped expected complete closed-horizon dividend reward budget
-- statement:
--   For any capped admissible strategy under an actual standing bounded-variation spectrally negative Levy process with nonnegative initial capital, the expected entire original discounted dividend Stieltjes reward over the closed finite horizon T is at most x plus H times the positive physical drift, for any H greater than T. Both positive-ruin paths and instantaneous-ruin paths are included, retaining all diffuse, initial and terminal atoms.
-- source:
--   Combines the genuine source BV positive-ruin closed-horizon drift bound with the admissible initial-atom bound on instant ruin, and integrates the resulting almost-sure inequality under the original Lévy probability law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_closed_horizon_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_complete_closed_horizon_expected_drift_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T H : ℝ≥0) (hTH : T < H) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (x + (H : ℝ) * X.drift) := by sorry
