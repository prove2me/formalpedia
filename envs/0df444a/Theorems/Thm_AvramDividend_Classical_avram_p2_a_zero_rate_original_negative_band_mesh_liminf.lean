-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_band_mesh_liminf
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_band_mesh_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:37:43.876727+00:00
-- url     : https://prove2.me/theorems/698d8e95-d726-4421-8ddb-eb64930e88af
-- title:
--   Original separated negative intrinsic jump count bounded by ENNReal mesh liminf
-- statement:
--   For every original spectrally negative Lévy path, T>0 and ε>0, the original intrinsic jump count on (0,T]×(-∞,-ε] is bounded by the ENNReal liminf of its negative uniform-grid increments below -ε/2. This applies the proved càdlàg path grid-liminf theorem to the genuine source left/right limits, original count-cardinality identity and the proved ENat-to-ENNReal liminf bridge, with no rate hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_uniform_path_negative_jump_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_enat_mesh_liminf_casts_to_ennreal

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_band_mesh_liminf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T)
    (ε : ℝ) (hε : 0 < ε) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ≤
    Filter.liminf (fun n : ℕ => (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ∞) : ℝ≥0∞)) atTop := by sorry
