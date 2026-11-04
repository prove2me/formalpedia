-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_physical_drift_exponential_integrable
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_physical_drift_exponential_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:27:39.227802+00:00
-- url     : https://prove2.me/theorems/a0a2cc0c-1b44-42a8-bb9c-80e4b7c553fe
-- title:
--   Actual BV Lévy drift-normalised finite-time exponential is integrable under original law
-- statement:
--   For the actual original BV spectrally negative Lévy source, its physical-drift-centred positive-frequency exponential is Bochner-integrable under the same probability law, including with infinite large-negative-jump first moment. Derived directly from X.laplace with a constant exponential factor.
-- source:
--   Exact original-process Lévy Laplace law X.laplace, deterministic factorisation of exp(θ(X_T−dT)), and Integrable.const_mul; no source jump compensator or auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original finite-horizon Levy Laplace law integrates the genuine
physical-drift-normalised exponential, including heavy negative tails. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_physical_drift_exponential_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω : Ω =>
      Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift))) P := by sorry
