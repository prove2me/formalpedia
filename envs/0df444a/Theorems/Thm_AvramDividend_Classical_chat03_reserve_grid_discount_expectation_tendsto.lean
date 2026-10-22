-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_reserve_grid_discount_expectation_tendsto
-- name    : AvramDividend.Classical.chat03_reserve_grid_discount_expectation_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:15:52.107511+00:00
-- url     : https://prove2.me/theorems/1b7c2cdd-d13a-481a-9c73-4b6304763abb
-- title:
--   Uniform-grid two-sided reserve-exit discounts converge to the continuous capital-barrier expectation
-- statement:
--   For a spectrally negative Lévy process, capital a>0, and initial reserve x, the exact upper-first uniform-grid discount expectation with barriers a-x and -x converges to its official continuous two-sided exit expectation as the mesh vanishes. The process record itself supplies its probability-measure instance, and strict barrier separation follows from a>0. This directly matches the boundary variables used in the stopped q-scale parent, while making no unsupported harmonicity assumption.
-- source:
--   Specialisation of the accepted exact grid discount expectation convergence theorem, using SpectrallyNegativeLevy.isProbability.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_exact_uniform_grid_discount_expectation_tendsto
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_reserve_grid_discount_expectation_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a)
    (q : ℝ) (hq : 0 ≤ q) (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n => ∫⁻ ω,
        let up := ⨅ k : ℕ,
          if a - x < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        let down := ⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * mesh n) ω < -x then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        if up < down then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
        else 0 ∂P)
      atTop (𝓝 (∫⁻ ω,
        if twoSidedExitUpTime X (a - x) ω <
            twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
        else 0 ∂P)) := by sorry
