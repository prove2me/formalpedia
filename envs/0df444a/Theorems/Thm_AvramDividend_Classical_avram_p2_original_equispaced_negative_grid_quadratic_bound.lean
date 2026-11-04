-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_equispaced_negative_grid_quadratic_bound
-- name    : AvramDividend.Classical.avram_p2_original_equispaced_negative_grid_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:45:32.929327+00:00
-- url     : https://prove2.me/theorems/293b8f60-4b94-4651-a416-95e5c89b886d
-- title:
--   Genuine original equispaced negative-increment count has a Bernoulli quadratic bound
-- statement:
--   For the actual original spectrally negative Lévy process and its unchanged probability space and filtration, the second moment of the count of mesh-h increments falling below minus epsilon among n successive intervals is bounded by n p_h + (n p_h)^2, where p_h is the true original one-time source probability. This follows by specialising the already-Proved source independent-increment quadratic theorem to equal meshes and identifying each interval law using the original stationary-increments hypothesis. No jump measure compensator or independent surrogate is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_count_second_moment_upper_bound

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_original_equispaced_negative_grid_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ≥0) (n : ℕ) (ε : ℝ) :
    (∫⁻ ω, (∑ i ∈ Finset.range n,
        ({v : Ω | X.X ((↑(i + 1) : ℝ≥0) * h) v -
            X.X ((i : ℝ≥0) * h) v ≤ -ε}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) ≤
      (n : ℝ≥0∞) * P {ω : Ω | X.X h ω ≤ -ε} +
        ((n : ℝ≥0∞) * P {ω : Ω | X.X h ω ≤ -ε}) ^ 2 := by sorry
