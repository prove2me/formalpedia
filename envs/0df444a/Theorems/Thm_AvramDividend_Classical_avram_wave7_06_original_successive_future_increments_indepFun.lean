-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_successive_future_increments_indepFun
-- name    : AvramDividend.Classical.avram_wave7_06_original_successive_future_increments_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:48:08.112418+00:00
-- url     : https://prove2.me/theorems/90be4700-66f5-4c84-8fcb-288c01d9d952
-- title:
--   Consecutive original Lévy increments are independent random variables
-- statement:
--   For any nonnegative s,u,v, the original consecutive increments over (s,s+u] and (s+u,s+u+v] are independent random variables under the original P. The intended proof derives σ-algebra containment for the earlier increment from adaptedness and uses source future-increment independence, with no auxiliary process.
-- source:
--   W7-06 original finite-grid two-cell independence interface for marked L² martingale construction; count extractor still requires separate measurable path law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_successive_future_increments_indepFun
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u v : ℝ≥0) :
    IndepFun
      (fun ω => X.X (s + u) ω - X.X s ω)
      (fun ω => X.X (s + u + v) ω - X.X (s + u) ω)
      P := by sorry
