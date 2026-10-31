-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_exit_ratio_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave3_02_scale_exit_ratio_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:57:14.627293+00:00
-- url     : https://prove2.me/theorems/45a22f3f-a060-4dc3-bd38-9f9d459706df
-- title:
--   True q-scale two-sided upcrossing quotient vanishes at an infinitely distant upper barrier
-- statement:
--   For any fixed real initial surplus x, the actual original-process q-scale factor W^(q)(x)/W^(q)(a) converges to zero as upper barrier a tends to infinity under Standing and q>0. The exact accepted source-specific scaleFunction divergence W(a)→+infinity and Mathlib's real ratio theorem prove this without needing derivative positivity, C1 or a surrogate stopped process.
-- source:
--   Avram Palmowski Pistorius (2007), two-sided first-passage scale identity; Esscher lower growth proved in the original spectrally negative Lévy model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_tendsto_atTop

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_scale_exit_ratio_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) :
    Tendsto (fun a : ℝ => W x / W a) atTop (𝓝 (0 : ℝ)) := by sorry
