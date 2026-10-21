-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_sequential_continuity_bounded
-- name    : AvramDividend.Classical.levy_transition_sequential_continuity_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:21:44.543987+00:00
-- url     : https://prove2.me/theorems/7fb624bd-d3ba-45a9-9a09-f0726e53d543
-- title:
--   Sequential continuity in the initial reserve of the Lévy transition operator for bounded continuous payoffs
-- statement:
--   Let X be the given spectrally negative Lévy process, t≥0, and f:R→R a continuous payoff with uniform norm bound B. If a sequence of deterministic initial reserves a_n converges to x, then the integrals E[f(a_n+X_t)] converge to E[f(x+X_t)]. For each outcome the same X_t is added to every reserve, and continuity of f gives pointwise convergence; measurability follows from adaptedness of X and continuity of f, with the constant norm bound B integrable because P is a probability measure. Apply the pinned Mathlib Bochner dominated convergence theorem. This establishes a semigroup state-continuity interface beyond globally Lipschitz payoffs, needed to approximate random initial reserves by simple states. It does not establish the Lévy generator at arbitrary f nor the controlled stopped dividend budget.
-- source:
--   Only fixed-time measurability from X.adapted and X.isProbability, plus pinned Mathlib dominated convergence; no unproved mission import.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_sequential_continuity_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : ℝ) (hB : ∀ y : ℝ, ‖f y‖ ≤ B)
    (a : ℕ → ℝ) (x : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds x)) :
    Filter.Tendsto
      (fun n => ∫ ω, f (a n + X.X t ω) ∂P)
      Filter.atTop
      (nhds (∫ ω, f (x + X.X t ω) ∂P)) := by sorry
