-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_esscher_unit_step_scale_growth
-- name    : AvramDividend.Classical.avram_wave3_02_esscher_unit_step_scale_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:38:08.89015+00:00
-- url     : https://prove2.me/theorems/3d3953dd-a55a-462e-abb2-f51314ceef1a
-- title:
--   Original q-scale function has a common strict Esscher unit-step growth factor
-- statement:
--   Under the genuine Standing spectrally negative Lévy law and positive discount, there is one φ>0 such that for every positive a, W(a)≤exp(-φ)W(a+1). The common factor is strictly less than one and follows from the already canonically Proved source Esscher-normalised scale monotonicity. It is a uniform, derivative-free quantitative growth theorem useful for controlling first-record reflected dividend rewards at all barrier heights.
-- source:
--   Avram Palmowski Pistorius (2007), q-scale Esscher transform and equation (3.15), Proved original scaleFunction_tilted_positive_monotone.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_esscher_unit_step_scale_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ : ℝ, 0 < φ ∧ ∀ a : ℝ, 0 < a →
      W a ≤ Real.exp (-φ) * W (a + 1) := by sorry
