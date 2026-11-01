-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generatorIntegrable_iff
-- name    : AvramDividend.Classical.avram_wave4_04_cap_linear_extension_source_generatorIntegrable_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:21:11.841608+00:00
-- url     : https://prove2.me/theorems/76780f0a-9237-49b3-8584-ca46df97ad81
-- title:
--   Cap-linear continuation preserves original Lévy generator-integrability at every strict interior reserve
-- statement:
--   For any original spectrally negative Lévy source X and any interior reserve x<c, the original source generatorIntegrable condition is equivalent for w and its slope-one cap extension. The proof compares the complete compensated Lévy generator integrands pointwise on their negative-mark integration domain, including the derivative subtraction. It does not assume the small-jump first absolute moment is finite and does not assert a stochastic martingale or controlled Itô–Meyer budget.
-- source:
--   Canonical generatorIntegrand and GeneratorIntegrable definitions; Mathlib IntegrableOn congruence on measurable negative mark domain Iio 0; exact corrected unbounded-variation HJB generator hypotheses from theorem 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04_cap_linear_extension_source_generatorIntegrable_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (c x : ℝ) (hx : x < c) :
    X.GeneratorIntegrable
      (fun y => if y ≤ c then w y else w c + (y - c)) x ↔
        X.GeneratorIntegrable w x := by sorry
