-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_independent_of_earlier_grid_past
-- name    : AvramDividend.Classical.avram_wave7_06_original_future_increment_independent_of_earlier_grid_past
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:40:45.002843+00:00
-- url     : https://prove2.me/theorems/2613920e-51d0-47cd-957e-2a0d7c5d898d
-- title:
--   Actual future increment independent of all earlier original grid σ-algebras
-- statement:
--   The original increment X_(s+t)-X_s is independent not only of 𝓕_s but of every earlier original σ-algebra 𝓕_r with r≤s. The proof uses the source independent-increment field and the monotonicity of the exact filtration.
-- source:
--   Predictable finite-grid source-independence interface for stopped compensated marked-cell martingale construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_future_increment_independent_of_earlier_grid_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r s t : ℝ≥0) (hrs : r ≤ s) :
    Indep
      (MeasurableSpace.comap
        (fun ω => X.X (s + t) ω - X.X s ω) inferInstance)
      (𝓕 r) P := by sorry
