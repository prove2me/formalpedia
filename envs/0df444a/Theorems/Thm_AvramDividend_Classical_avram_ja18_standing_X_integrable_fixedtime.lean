-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_standing_X_integrable_fixedtime
-- name    : AvramDividend.Classical.avram_ja18_standing_X_integrable_fixedtime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T20:11:38.485477+00:00
-- url     : https://prove2.me/theorems/ecbf4e66-0b0f-406b-8dc4-7819893f9c00
-- title:
--   Standing integrability of original Lévy state at any fixed time
-- statement:
--   For an original spectrally negative Lévy process with Standing, finite first moment at t=1 and positive exponential moments imply L1 integrability of X_t at every deterministic t≥0. Split t into integer and fractional times; for r∈[0,1], bound negative X_r by negative X_1 plus the positive future increment X_1−X_r, whose law is X_(1−r).
-- source:
--   New sound analytic helper for 70393ec7, with original Ω/P/filtration and without a Lévy–Itô or Brownian representation. No finite jump-intensity premise is needed for this part.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_standing_X_integrable_fixedtime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    ∀ t : ℝ≥0, Integrable (X.X t) P := by sorry
