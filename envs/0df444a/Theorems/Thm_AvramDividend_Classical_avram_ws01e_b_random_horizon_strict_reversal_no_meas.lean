-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_random_horizon_strict_reversal_no_meas
-- name    : AvramDividend.Classical.avram_ws01e_b_random_horizon_strict_reversal_no_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T07:43:27.992148+00:00
-- url     : https://prove2.me/theorems/0c560361-7634-4b23-957d-99da64289e40
-- title:
--   Strict Lévy drawdown and infimum reversal at an independent random horizon without measurability hypotheses
-- statement:
--   For a genuine spectrally negative Lévy process and independently sampled nonnegative random horizon, terminal drawdown and running-infimum strict-threshold event probabilities agree without separately assuming joint event measurability. The latter is derived from path right-continuity, jointly measurable Lévy trajectories and dyadic event detection, and the equality follows from the already-Proved independent-horizon reversal theorem. The result is under the original Lévy law and does not assert Wiener–Hopf factorisation under a tilted law.
-- source:
--   Proved avram_ws01e_b_independent_random_horizon_strict_reversal (83aab0f5), conditional on the new Lévy joint event measurability interface.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_random_horizon_strict_events_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_random_horizon_strict_reversal

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_random_horizon_strict_reversal_no_meas
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Q : Measure Θ) [SFinite Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (a : ℝ) :
    (P.prod Q) {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X (e z.2) z.1 - X.X s z.1 < a} =
    (P.prod Q) {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X s z.1 - X.X 0 z.1 < a} := by sorry
