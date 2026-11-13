-- Prove2me | Theorems.Thm_DuchiSIT_tv_probability_bounds
-- name    : DuchiSIT.tv_probability_bounds
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T18:18:24.31311+00:00
-- url     : https://prove2.me/theorems/bf2d12d4-7971-43ae-abff-8ebc9366244d
-- title:
--   Event bounds and definiteness of total variation for probability measures
-- statement:
--   Let $\mu,\nu$ be probability measures on an arbitrary measurable space, with total variation defined by the supremum of absolute measurable-event differences. Then
--
--   $$|\mu(A)-\nu(A)|\le d_{TV}(\mu,\nu)\quad(A\text{ measurable}),\qquad0\le d_{TV}(\mu,\nu)\le1,$$
--
--   $$d_{TV}(\mu,\nu)=0\quad\Longleftrightarrow\quad\mu=\nu.$$
--
--   These bounds justify the real suprema and positive denominators in the Dobrushin coefficient and the strong total-variation data-processing coefficient. No separation or topology is assumed on the measurable space.
-- source:
--   John Duchi, Lecture Notes on Statistics and Information Theory, December 6, 2023, Section 2.2, equation (2.2.6) and Lemma 2.2.4, printed pp.24–25; supporting event-supremum properties for Proposition 9.1.1, printed pp.221–222. https://web.stanford.edu/class/stats311/lecture-notes.pdf

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
open MeasureTheory

namespace DuchiSIT
theorem tv_probability_bounds {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ A : Set X, MeasurableSet A → |(μ A).toReal - (ν A).toReal| ≤ MarkovChainCLT.tvDist μ ν) ∧
    0 ≤ MarkovChainCLT.tvDist μ ν ∧ MarkovChainCLT.tvDist μ ν ≤ 1 ∧
    (MarkovChainCLT.tvDist μ ν = 0 ↔ μ = ν) := by sorry
end DuchiSIT
