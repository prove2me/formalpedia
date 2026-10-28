-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_strict_survival_le_exp_first_jump
-- name    : AvramDividend.Classical.bv_reflected_ruin_strict_survival_le_exp_first_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T16:30:40.366291+00:00
-- url     : https://prove2.me/theorems/c82fc1f3-2898-4b4c-8b64-9e45226a7bad
-- title:
--   Actual finite-activity strict zero-barrier survival is bounded above by first-jump exponential law
-- statement:
--   For a bounded-variation finite-activity spectrally negative Lévy process, the probability of strict survival of the actual zero-barrier reflected drawdown stopping time beyond any given t is at most exp(-λt). On strict-survival paths, the positive drift-residual event has probability zero by the accepted grid-mesh theorem. Negative drift residual is almost surely impossible by the accepted drift-upper law. Partition on the three possible signs of the residual, then use the accepted exponential probability of zero residual. This supplies the upper half of the true first-jump stopping-time law.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3, equation (3.14). Prove2Me actual-process zero-residual and strict-survivor grid-probability results.

import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_reflected_ruin_strict_survival_le_exp_first_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} ≤
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
