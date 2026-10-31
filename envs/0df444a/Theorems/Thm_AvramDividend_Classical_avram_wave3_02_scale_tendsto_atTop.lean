-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_tendsto_atTop
-- name    : AvramDividend.Classical.avram_wave3_02_scale_tendsto_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:48:52.051495+00:00
-- url     : https://prove2.me/theorems/5015078a-b08b-4c8a-b826-b15f7fd0a008
-- title:
--   Original positive-discount q-scale function diverges at high reserves without C1 assumptions
-- statement:
--   The genuine q-scale function W^(q) for the original Standing spectrally negative Levy process at q>0 tends to +infinity as the capital tends to +infinity. The already Proved source exponential lower growth W(a)≥W(1) exp(φ(a−1)) for a≥1 and positive W(1), together with Mathlib real exponential divergence, yields this result without global scale C1 or derivative assumptions. It supports high-reserve valuation analysis and finite-barrier research.
-- source:
--   Kuznetsov Kyprianou Rivero (2012), Esscher scale growth; Avram Palmowski Pistorius (2007) scale function construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_exp_lower_growth
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_scale_tendsto_atTop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Tendsto W atTop atTop := by sorry
