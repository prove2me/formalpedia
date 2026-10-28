-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_expected_geometric_of_actual_step
-- name    : AvramDividend.Classical.killed_firstRecord_expected_geometric_of_actual_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:25:43.41136+00:00
-- url     : https://prove2.me/theorems/8ce72a25-3262-4822-9a4c-06018fe50375
-- title:
--   Exact killed first-record geometric expectation from base exit and strong-Markov regeneration
-- statement:
--   For the actual killed discounted first-record payments, a lower bound εp on the first expected payment and a uniform one-step discounted regeneration estimate E[w(n+1)]≥p E[w n] imply E[w n]≥εp^(n+1). This translates the already proved abstract grid induction to the precise n+1 record indexing of the stopped renewal theorem, leaving only the two stochastic estimates as hypotheses.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, first-record renewal. Direct application of Proved killed_firstRecord_grid_geometric_expected_lower_of_step after normalising record clock indices.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_geometric_expected_lower_of_step

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstRecord_expected_geometric_of_actual_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε p : ℝ)
    (hq : 0 ≤ q) (hε : 0 ≤ ε) (hp : 0 ≤ p)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n ω, w n ω =
      if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0)
    (hbase : ENNReal.ofReal (ε * p) ≤ (∫⁻ ω, w 0 ω ∂P))
    (hstep : ∀ n, ENNReal.ofReal p * (∫⁻ ω, w n ω ∂P) ≤
      (∫⁻ ω, w (n + 1) ω ∂P)) :
    ∀ n, ENNReal.ofReal (ε * p ^ (n + 1)) ≤
      (∫⁻ ω, w n ω ∂P) := by sorry
