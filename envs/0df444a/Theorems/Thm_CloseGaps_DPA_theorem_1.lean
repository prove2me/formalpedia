-- Prove2me | Theorems.Thm_CloseGaps_DPA_theorem_1
-- name    : CloseGaps.DPA.theorem_1
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:35:52.521072+00:00
-- url     : https://prove2.me/theorems/899ae076-748b-447f-b5f0-90c50fca5fdd
-- title:
--   Theorem 1 — Uniform near-optimal regret for DPA
-- statement:
--   Theorem 1. Let Assumption 1 hold for Γ = Γ(M, K,
--   m_L, m_U). Then there exists an admissible policy π generated
--   by Algorithm DPA, such that for all n ≥ 1,
--
--   sup_{λ∈Γ} R_n^π(x,T;λ) ≤ C(log n)^{4.5}/√n
--
--   for some constant C.
--
--   Differences from the source:
--   - encoding: Continuous-time controlled Poisson sales with an off action. → A measurable price rule on sale histories, exponential interarrivals and Option-valued actions.; reason: The off action has zero intensity and revenue; the history rule cannot access the unknown demand.
--   - reading: The size parameter n is written without an integrality restriction. → n is real.; reason: This retains the displayed domain, including every integer size.
--   - encoding: The DPA objects are constructed by the displayed algorithm. → Partial stage construction and successful construction in the conclusion.; reason: Definedness is asserted in the conclusion at the source sizes: every printed real grid count must be an exact positive integer, each stage duration positive, and each stopping minimum attained; no rounding or restriction to executable sizes is introduced.
--   - encoding: A supremum of regrets over the demand class. → The same C bounds the regret for every member of the full class.; reason: Pointwise uniform comparison avoids empty or unbounded real-supremum defaults.
--   - encoding: General T and feasible price interval. → Multiplicative price and time normalization in the algorithm, with the physical fluid benchmark.; reason: Multiplication preserves revenue ordering; C remains outside the price-interval quantifier.
--   - encoding: Inventory sales are integral and at most nx. → The stochastic sale cap is floor(nx); the fluid inventory remains nx.; reason: These are the same unit-sales constraint, without restricting real initial inventory.
--   - reading: Stage counts appear as fixed summation limits and deterministic factors outside expectations in section 5, although the interval widths are random. → A common pair of deterministic counts satisfies the actual stopping tests almost surely on the constructed virtual traces.; reason: This is the literal fixed-count reading of the printed formulas; nominal-width equalities are not assumed, and successful construction is asserted in the conclusion.
--   - encoding: Grid prices have indices j=1,...,κ_i. → Grid indices are j=0,...,k-1, with price lo+j(hi-lo)/k.; reason: The same left endpoints are enumerated; only the index origin changes.
--   - reading: The empirical argmax and argmin do not specify a tie rule. → Choose the least grid index attaining each finite optimum.; reason: This fixes an observable deterministic selection from the source argmax or argmin, without demand information.
--   - reading: The base-instance estimator is count/Δ and its inventory target is x/T. → For the size-n normalized instance, estimate base demand by count/(nΔ) and compare with x.; reason: Instantiating the pseudocode with inventory nx and dividing its rate estimate and target by n gives this rule; normalized time has horizon one.
-- source:
--   Wang, Deng, and Ye (2014), Operations Research 62(2), 318–331, DOI 10.1287/opre.2013.1245, Theorem 1, p. 322 (PDF 5)

import Definitions.Def_CloseGaps_DPA_RevenueEvents

open MeasureTheory Set

open scoped Classical

namespace CloseGaps.DPA

theorem theorem_1 (c : Coefficients) (hc : c.Positive)
    (x T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Market, a.Valid →
      ∃ π : ℝ → PriceRule, ∀ n : ℝ, 1 ≤ n →
        ∀ lam : ℝ → ℝ, InClass c a x T lam →
          (∃ N : StageCounts, generated a lam n x T (π n) N) ∧
          admissible a lam n x T (π n) ∧
          (fluidRevenues a x T lam).Nonempty ∧ BddAbove (fluidRevenues a x T lam) ∧
          0 < fluidValue a x T lam ∧
          1 - expectedRevenue (π n) lam n x T / (n * fluidValue a x T lam) ≤
            C * (Real.log n) ^ (9 / 2 : ℝ) / Real.sqrt n := by sorry

end CloseGaps.DPA
