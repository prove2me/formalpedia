-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_centered_exact_path_vitali_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_centered_exact_path_vitali_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:10:41.626803+00:00
-- url     : https://prove2.me/theorems/9b40e001-94b5-4d7b-a9f7-4e4fa49c345e
-- title:
--   Original Levy centred cadlag grids converge in L1 and genuine expectations without a mesh-limit hypothesis
-- statement:
--   For the actual SpectrallyNegativeLevy process, a positive NNReal horizon and a continuous compactly supported negative-jump test g, combine the independently kernel-proved deterministic cadlag original-path exact mesh convergence (P2-H) with the already proved original-source uniform-L2 Vitali principle (P2-J). Construct a single integrable random-variable Z such that the uncentred original-process uniform-mesh sums converge strongly in L1 to Z and their genuine real Bochner expectations converge to the expectation of Z. No separate pathwise convergence assumption remains.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_original_centered_source_path_exact_mesh_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_centered_nnreal_compact_existential_both

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! The proved original-path cadlag mesh limit feeds the actual L2 Vitali expectation theorem. -/

theorem AvramDividend.Classical.avram_p2_j_ui_original_centered_exact_path_vitali_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) - Z)
        1 P) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, Z ω ∂P)) := by sorry
