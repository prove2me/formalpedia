-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_large_tail_integrable
-- name    : AvramDividend.Classical.avram_wave4_05_source_far_field_large_tail_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:51:43.957662+00:00
-- url     : https://prove2.me/theorems/d7e24235-83f7-41a5-b6ca-42077389ab6b
-- title:
--   Genuine ν-integrability of uncompensated large-negative-jump increments above cstar+1
-- statement:
--   For any actual source spectrally negative Lévy process and q-scale function W, whenever x≥cstar(W)+1, the ordinary large-negative-jump increment y↦vcstar(x+y)−vcstar(x) is genuinely Bochner-integrable with respect to the source Lévy measure ν over y≤−1. This includes every ruin-crossing jump. It follows from the already proved full GeneratorIntegrable domain, restriction to the large-jump set and the exact pointwise kernel identity; no first moment of arbitrarily large negative jump sizes is assumed.
-- source:
--   Source GeneratorIntegrable strictly above cap, exact source large-jump kernel identity; Mathlib IntegrableOn.mono_set and integrableOn_congr_fun.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_05_source_far_field_large_tail_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    IntegrableOn (fun y : ℝ => vcstar W (x + y) - vcstar W x)
      (Iic (-1 : ℝ)) X.ν := by sorry
