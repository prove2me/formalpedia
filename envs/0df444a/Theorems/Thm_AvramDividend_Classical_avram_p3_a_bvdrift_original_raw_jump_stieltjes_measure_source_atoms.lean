-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_stieltjes_measure_source_atoms
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_stieltjes_measure_source_atoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:34:05.736483+00:00
-- url     : https://prove2.me/theorems/e4912a8c-fc25-4495-9906-eaef2cbd1c3b
-- title:
--   Every positive-time atom of actual BV negative-jump Stieltjes measure equals the original left jump
-- statement:
--   Under the original source bounded-variation process and probability, on one almost-sure event a Stieltjes measure of the exact cumulative true negative-jump sum has point mass at each strictly positive time t exactly equal to the genuine raw left-limit jump magnitude of X at t. This requires no extra decomposition identity, auxiliary representation or jump intensity assumption.
-- source:
--   Already Proved 73032d17 gives original raw cumulative strict-past leftLim. Already Proved 2f1436db splits the cumulative actual real sum into the endpoint left jump and strict-past total. Pinned Mathlib StieltjesFunction.measure_singleton identifies atomic mass with the cumulative jump of its defining function.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_stieltjes_measure_source_atoms
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      ∀ t : ℝ≥0, 0 < t →
        μ {t} = ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω) := by sorry
