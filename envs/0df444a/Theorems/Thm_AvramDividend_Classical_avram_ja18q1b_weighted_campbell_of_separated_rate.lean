-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18q1b_weighted_campbell_of_separated_rate
-- name    : AvramDividend.Classical.avram_ja18q1b_weighted_campbell_of_separated_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:13:38.869143+00:00
-- url     : https://prove2.me/theorems/d7f55bb5-c0df-4844-ac4a-23c86d7b6d28
-- title:
--   Weighted intrinsic Campbell identity from all separated Borel count-rate equalities
-- statement:
--   Pure nonnegative integration/monotone class step. Given exact original expected counts for every separated-negative Borel mark set, extend by simple functions and monotone convergence to the unbounded weight |z| on z≤-1.
-- source:
--   J-A18 Q1: isolates the generic Giry-measure integration step from the stochastic identification proved in q1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18q1b_weighted_campbell_of_separated_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0)
    (hRate : ∀ B : Set ℝ, MeasurableSet B → B ⊆ Iic (-1 : ℝ) →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
       0 < u ∧ X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u, X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B) ∂P) =
        (t : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω, ∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
      ENNReal.ofReal |p.2| ∂((Measure.count.restrict {u : ℝ≥0 |
       0 < u ∧ X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u, X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
      (t : ℝ≥0∞) *
      (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) := by sorry
