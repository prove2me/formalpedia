-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_null_events_iff
-- name    : AvramDividend.Classical.chat04_esscher_finite_horizon_null_events_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:17:45.78558+00:00
-- url     : https://prove2.me/theorems/abd6d3fb-7692-4c69-90ca-9c5a8f7f6ca4
-- title:
--   Every finite Esscher law has exactly the same null events as the original Lévy law
-- statement:
--   For every deterministic horizon, every real exponential tilt parameter, and every measurable-space event A, the genuine Esscher density-weighted measure assigns zero mass to A if and only if the original Lévy measure does. Strict positivity of the Esscher Radon–Nikodym factor ensures equivalence of null sets, preserving almost-sure path regularity and the absence of positive jumps at every finite horizon.
-- source:
--   Apply the pinned Mathlib `withDensity_apply_eq_zero` and measurable positive exponential density, with `X.adapted.measurable` and ENNReal.ofReal_pos. This is finite-horizon mutual absolute continuity, not an unproved global Esscher change of measure.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Process.Adapted
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_finite_horizon_null_events_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (θ : ℝ) (A : Set Ω) :
    (P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X t ω - (t : ℝ) * X.ψ θ)))) A = 0 ↔ P A = 0 := by sorry
