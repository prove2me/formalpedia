-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_extension_source_negative_jump_generatorIntegrand
-- name    : AvramDividend.Classical.avram_wave4_04_cap_extension_source_negative_jump_generatorIntegrand
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:13:42.23388+00:00
-- url     : https://prove2.me/theorems/8ae56d07-c5bb-41f2-a359-7383f8c32695
-- title:
--   Cap-linear continuation preserves the exact source compensated negative-jump generator integrand
-- statement:
--   The actual spectrally negative Lévy source generator uses only negative marks. For every interior reserve x<c and negative jump z≤0, extending w linearly with slope one above the cap leaves the full compensated generator integrand unchanged, including the derivative correction. The derivative agreement follows from genuine local equality on a neighbourhood of x. This prepares a noncircular cap boundary continuation under the existing original-source generator/HJB hypotheses, without proving any stochastic integral or full verification.
-- source:
--   SpectrallyNegativeLevy.generatorIntegrand source definition in Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy; cap extension from corrected UBV target 429e17ca-5528-40b5-b593-7c03973d0706 and source negative jump support X.ν(Ici 0)=0. Equality on negative marks is the local-value-plus-first-derivative part of generator preservation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04_cap_extension_source_negative_jump_generatorIntegrand
    (w : ℝ → ℝ) (c x z : ℝ) (hx : x < c) (hz : z ≤ 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun y => if y ≤ c then w y else w c + (y - c)) x z =
        SpectrallyNegativeLevy.generatorIntegrand w x z := by sorry
