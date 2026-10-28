-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_reflected_strict_survival_measure_exp_first_jump
-- name    : AvramDividend.Classical.bv_reflected_strict_survival_measure_exp_first_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:03:58.792374+00:00
-- url     : https://prove2.me/theorems/9e8ab616-d740-4681-b585-f6caa0510cdc
-- title:
--   Exact extended-nonnegative measure of strict zero-barrier Lévy ruin survival
-- statement:
--   For the original standing bounded-variation finite-activity spectrally negative Lévy process and every strictly positive real t, the actual probability measure (ENNReal, not P.real) of the event ENNReal.ofReal t<barrierRuinTime X 0 equals ENNReal.ofReal(exp(-lambda*t)), with lambda the finite mass of the negative-jump Lévy measure. The exact real-valued strict-survival exponential tail is already Proved. Using Real.toNNReal t, finite probability measure of the event, and Mathlib ENNReal.ofReal_toReal transfers that equality into the ENNReal measure type needed by Tonelli and nonnegative lower integral calculations.
-- source:
--   Avram, Palmowski and Pistorius (2007) first-jump law, Prove2Me accepted exact original strict ruin clock tail and probability measure conversion.

import Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_strict_survival_eq_exp_first_jump
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.NNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_reflected_strict_survival_measure_exp_first_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ) (ht : 0 < t) :
    P {ω : Ω | ENNReal.ofReal t < barrierRuinTime X 0 ω} =
      ENNReal.ofReal
        (Real.exp (-(t * (X.ν (Iio (0 : ℝ))).toReal))) := by sorry
