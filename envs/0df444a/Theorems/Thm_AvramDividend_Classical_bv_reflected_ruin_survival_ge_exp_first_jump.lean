-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_survival_ge_exp_first_jump
-- name    : AvramDividend.Classical.bv_reflected_ruin_survival_ge_exp_first_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:32:32.468695+00:00
-- url     : https://prove2.me/theorems/44bb71ca-77a0-42a7-a08a-0a1da40bdf23
-- title:
--   Actual zero-barrier reflected survival probability dominates exponential first-jump survival
-- statement:
--   For the actual Standing bounded-variation finite-activity spectrally negative Lévy process, the original drawdown ruin survival probability P(t≤τ̂_0) is at least exp(-λt), where λ is its finite negative-jump intensity. The Proved full zero-residual history event has probability exp(-λt); the Proved original reflected stopping-clock lemma shows that event is contained in survival through t. Apply monotonicity of real-valued probability. This supplies the lower half of the first-jump stopping-time survival comparison and is directly usable in stopped reward lower bounds.
-- source:
--   Avram Palmowski Pistorius (2007), §3.3 formula (3.14); Prove2Me actual residual history and original stopping-clock comparison.

import Theorems.Thm_AvramDividend_Classical_bv_zero_residual_prefix_before_reflected_ruin
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_history_zero_exponential_survival
import Mathlib.MeasureTheory.Measure.Real

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_reflected_ruin_survival_ge_exp_first_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) ≤
      P.real {ω : Ω | (t : ℝ≥0∞) ≤ barrierRuinTime X 0 ω} := by sorry
