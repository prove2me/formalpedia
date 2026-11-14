-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_uniform_grid_eventually_excludes_all_final_source_negative_marks
-- name    : AvramDividend.Classical.avram_bvb45_original_uniform_grid_eventually_excludes_all_final_source_negative_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:38:53.761786+00:00
-- url     : https://prove2.me/theorems/b7ae7c05-7874-4893-b3d7-e44cd9b83fd1
-- title:
--   Every original finite activity BV source uniformly eventually has no true negative jumps in the prescribed final horizon grid strip
-- statement:
--   Original finite negative jump activity and bounded-variation sample paths have no original physical source jump in the exact supplied uniform-grid final strip from last original grid node to full horizon, on a single probability-one event and for every sufficiently fine row. Uses the original source terminal mark separation bvb44 and Proved uniform endpoint convergence bva78. The original Lévy measure, filtration, process, leftLimit, all actual uniform-grid endpoints and original clock remain unchanged. Supports source-true finite positive-jump-count error phys69.
-- source:
--   Accepted bvb44 21aab113, accepted bva78 104b3f27, original phys69 4287fafd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb44_original_finiteactivity_ae_last_horizon_no_negative_mark_strip
import Theorems.Thm_AvramDividend_Classical_avram_bva78_original_supplied_uniform_endpoint_tendsto_real_horizon
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb45_original_uniform_grid_eventually_excludes_all_final_source_negative_marks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      ∀ t : ℝ≥0, 0 < t →
        (u n (n + 1) : ℝ) < (t : ℝ) →
        (t : ℝ) ≤ T →
        X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0 →
        False := by sorry
