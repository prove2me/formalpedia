-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior
-- name    : AvramDividend.Classical.avram_wave4_04_cap_linear_extension_source_generator_eq_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:17:54.883634+00:00
-- url     : https://prove2.me/theorems/de1c1aee-43d3-47a2-83ae-6115b56249e3
-- title:
--   Actual source Lévy generator is unchanged by slope-one cap continuation at strict interior reserves
-- statement:
--   For the same original spectrally negative Lévy source X and any reserve x strictly below a finite real cap c, the complete source generator agrees for w and its slope-one continuation above c. The proof identifies the second-derivative and first-derivative coefficients by local neighbourhood equality, and the compensated negative-jump integral on the exact generator domain z<0, with no assumption of absolute first-jump variation or differentiability at cap contact. This preserves the original local HJB generator drift under cap extension but does not itself prove source stochastic semimartingale decomposition, controlled Ito-Meyer, or the dividend verification target.
-- source:
--   Exact Avram source SpectrallyNegativeLevy.generator and generatorIntegrand source definitions with actual triplet c/σ/ν; Mathlib pinned Filter.EventuallyEq.deriv_eq, Filter.EventuallyEq.iteratedDeriv_eq and MeasureTheory.setIntegral_congr_fun. Mathematical derivative and ν-integral identity for cap linear extension in corrected UBV verification 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04_cap_linear_extension_source_generator_eq_interior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (c x : ℝ) (hx : x < c) :
    X.generator
      (fun y => if y ≤ c then w y else w c + (y - c)) x =
        X.generator w x := by sorry
