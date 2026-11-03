-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_L2_integrable_and_equal_second_moment
-- name    : AvramDividend.Classical.avram_wave7_06_original_future_increment_L2_integrable_and_equal_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:35:45.699199+00:00
-- url     : https://prove2.me/theorems/03494ff8-3175-4d43-9e2e-372324b52d47
-- title:
--   Actual original future increment retains L² integrability and exact second moment
-- statement:
--   Assuming the original zero-origin increment X_t has finite second moment under P, every genuine future increment X_(s+t)-X_s on the same sample space has finite second moment and the same expected square. This transfers L² integrability and variance precursor information using the source stationary law.
-- source:
--   Source-specific future-increment L² moment transport for W7-06 marked-cell construction. It does not assume the small-jump factorial moment or compensate an unproved process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_future_increment_L2_integrable_and_equal_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hInt : Integrable (fun ω => (X.X t ω) ^ (2 : ℕ)) P) :
    Integrable
      (fun ω => (X.X (s + t) ω - X.X s ω) ^ (2 : ℕ)) P ∧
    (∫ ω, (X.X (s + t) ω - X.X s ω) ^ (2 : ℕ) ∂P) =
      ∫ ω, (X.X t ω) ^ (2 : ℕ) ∂P := by sorry
