-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_leftlimit_strict_positive_mesh_for_all_original_paths
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_leftlimit_strict_positive_mesh_for_all_original_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:21:24.544348+00:00
-- url     : https://prove2.me/theorems/6a28f07b-5329-41f4-bd0e-e07c81138027
-- title:
--   A single strictly increasing original-time grid recovers every source Lévy pre-jump value pathwise
-- statement:
--   For each deterministic positive time t, there exists one strictly increasing positive-time grid approaching t from below, chosen independently of the sample, such that the genuine source values X(grid n, ω) converge to the original pre-jump left limit X(t-, ω) for every ω. The result uses only the original path left-limit field, a dense-order sequence theorem and filter composition; no BV, Poisson representation, change of probability space or filtration is involved. It supplies a deterministic countable same-path left-limit extractor needed to build source marked-count functionals from future paths.
-- source:
--   Actual SpectrallyNegativeLevy P 𝓕 field X.leftLim; pinned Mathlib Dense.exists_seq_strictMono_tendsto_of_lt and tendsto_leftLim_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_leftlimit_strict_positive_mesh_for_all_original_paths
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ grid : ℕ → ℝ≥0,
      StrictMono grid ∧
      (∀ n, 0 < grid n ∧ grid n < t) ∧
      Tendsto grid atTop (𝓝[<] t) ∧
      ∀ ω : Ω,
        Tendsto (fun n => X.X (grid n) ω) atTop
          (𝓝 (Function.leftLim (fun u : ℝ≥0 => X.X u ω) t)) := by sorry
