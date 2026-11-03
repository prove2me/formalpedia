-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_X_integrable_mean_additivity
-- name    : AvramDividend.Classical.avram_wave7_06_original_X_integrable_mean_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:04:37.770186+00:00
-- url     : https://prove2.me/theorems/0789fc09-ffd8-4a0e-9f51-505c504c8963
-- title:
--   Canonical Levy X original first moments add in time and preserve integrability
-- statement:
--   If original X_s and X_t have finite first moments, actual X_(s+t) is integrable and its original P mean equals E[X_s]+E[X_t]. Proof uses the already Proved original stationary future-increment L1 identity and a pointwise exact additive decomposition; no generator approximation or external process.
-- source:
--   W7-06 original compensated-X martingale mean preparation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_X_integrable_mean_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hStart : Integrable (X.X s) P)
    (hFuture : Integrable (X.X t) P) :
    Integrable (X.X (s + t)) P ∧
    (∫ ω, X.X (s + t) ω ∂P) =
      (∫ ω, X.X s ω ∂P) + (∫ ω, X.X t ω ∂P) := by sorry
