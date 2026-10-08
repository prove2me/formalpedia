-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable
-- name    : AvramDividend.Classical.levy_large_negative_jump_unit_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:25:31.22478+00:00
-- url     : https://prove2.me/theorems/30dea431-675a-4b89-b99d-07a60ff19abd
-- title:
--   Finite large-negative-jump mass from the canonical Lévy integrability bound
-- statement:
--   Every canonical spectrally negative Lévy process satisfying its Lévy-measure integrability field has integrable constant-one function on jumps y≤−1, so the measure of the large-negative-jump region is finite. This supplies exactly the missing large-jump integrability hypothesis in the analytic lower bound for its Laplace exponent.
-- source:
--   The exact canonical ν_integrable field on min(1,y²); pinned Mathlib lintegral_ofReal_ne_top_iff_integrable and IntegrableOn.congr_fun on Iic(-1), where min(1,y²)=1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_large_negative_jump_unit_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (-1 : ℝ)) X.ν := by sorry
