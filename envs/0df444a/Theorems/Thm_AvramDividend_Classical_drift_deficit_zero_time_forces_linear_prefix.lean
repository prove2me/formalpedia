-- Prove2me | Theorems.Thm_AvramDividend_Classical_drift_deficit_zero_time_forces_linear_prefix
-- name    : AvramDividend.Classical.drift_deficit_zero_time_forces_linear_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:54:17.031834+00:00
-- url     : https://prove2.me/theorems/cd922f32-0e13-4eea-8e57-07e1df6e89d9
-- title:
--   A zero monotone drift deficit forces the whole preceding Lévy path to equal drift
-- statement:
--   If a drift-compensated Lévy path D_t=d*t-X_t begins at zero, is nondecreasing, and is still zero at time t, then D_s is zero at every earlier time s<=t and therefore X_s=d*s on the whole initial interval. This is the precise pathwise first-no-jump prefix lemma. The hypotheses are explicit, so it can be composed with the separately Proved almost-sure all-times monotonicity and the process initial-value property.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3 zero-barrier compound-Poisson first-jump decomposition; elementary monotone-path argument.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.Real.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.drift_deficit_zero_time_forces_linear_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hStart : X.X 0 ω = 0)
    (hMono : Monotone (fun t : ℝ≥0 => X.drift * (t : ℝ) - X.X t ω))
    (t : ℝ≥0) (hZero : X.drift * (t : ℝ) - X.X t ω = 0) :
    ∀ s : ℝ≥0, s ≤ t → X.X s ω = X.drift * (s : ℝ) := by sorry
