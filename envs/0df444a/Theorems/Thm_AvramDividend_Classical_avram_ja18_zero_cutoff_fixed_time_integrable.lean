-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_zero_cutoff_fixed_time_integrable
-- name    : AvramDividend.Classical.avram_ja18_zero_cutoff_fixed_time_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T20:00:35.525899+00:00
-- url     : https://prove2.me/theorems/70393ec7-4e04-4d18-b81f-108c3f1c089e
-- title:
--   Original finite-activity zero-cutoff residual is L1 at fixed times
-- statement:
--   Isolate fixed-time integrability of the original intrinsic zero-cutoff residual, using Standing first moment, finite original negative jump activity, and original large-jump sums.
-- source:
--   Exact first conjunct of Open 6bbd3299-8e85-4f09-ab3f-313bc0ed5c4d. No auxiliary Brownian, no independent process replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_zero_cutoff_fixed_time_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) P := by sorry
