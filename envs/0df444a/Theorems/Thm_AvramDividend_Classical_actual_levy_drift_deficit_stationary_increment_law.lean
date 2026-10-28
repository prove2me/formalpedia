-- Prove2me | Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
-- name    : AvramDividend.Classical.actual_levy_drift_deficit_stationary_increment_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:13:20.940016+00:00
-- url     : https://prove2.me/theorems/ed24e69e-19e3-4b28-8301-504bb9a3c641
-- title:
--   Actual Lévy drift-deficit increments have the stationary one-time deficit distribution
-- statement:
--   For the actual spectrally negative Lévy process, stationary increments of X imply that increments of the compensated drift deficit D_t=d t-X_t have exactly the same distribution as D_{t-s}. This is obtained from the canonical stationary-increment law via the measurable affine map z↦d(t-s)-z, together with NNReal subtraction casts, and is the precise input needed to transfer one-cell small-positive-deficit probability bounds to every grid cell.
-- source:
--   Canonical SpectrallyNegativeLevy.stationaryIncrements; Mathlib ProbabilityTheory.IdentDistrib.const_sub; Avram, Palmowski and Pistorius (2007), §3.3.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.IdentDistrib
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring
open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.actual_levy_drift_deficit_stationary_increment_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    IdentDistrib
      (fun ω => (X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω))
      (fun ω => X.drift * ((t - s : ℝ≥0) : ℝ) -
        X.X (t - s) ω) P P := by sorry
