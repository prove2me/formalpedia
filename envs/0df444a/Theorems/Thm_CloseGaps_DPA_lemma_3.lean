-- Prove2me | Theorems.Thm_CloseGaps_DPA_lemma_3
-- name    : CloseGaps.DPA.lemma_3
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:35:57.709017+00:00
-- url     : https://prove2.me/theorems/04c8cca9-1df1-402b-b46e-de82b54b9bbb
-- title:
--   Lemma 3 — Optimal-price containment and regime switch
-- statement:
--   Lemma 3. Let p^D be the optimal price for the deterministic
--   problem. Define A_0 to be the event satisfying the following
--   conditions:
--   1. If we never enter Step 3, then p^D ∈ I_i^u for all i =
--   1, 2, …, N^u.
--   2. If Step 2 stops at i_0 and the algorithm enters Step 3,
--   then p^c ≥ p^u, p^D ∈ I_i^u for all i = 1, 2, …, i_0 and p^D ∈ I_j^c
--   for all j = 1, 2, …, N^c.
--   Then P(A_0) = 1 − O(1/n).
--
--   Differences from the source:
--   - encoding: Continuous-time controlled Poisson sales with an off action. → A measurable price rule on sale histories, exponential interarrivals and Option-valued actions.; reason: The off action has zero intensity and revenue; the history rule cannot access the unknown demand.
--   - reading: The size parameter n is written without an integrality restriction. → n is real.; reason: This retains the displayed domain, including every integer size.
--   - encoding: The DPA objects are constructed by the displayed algorithm. → Partial stage construction and successful construction in the conclusion.; reason: Definedness is asserted in the conclusion at the source sizes: every printed real grid count must be an exact positive integer, each stage duration positive, and each stopping minimum attained; no rounding or restriction to executable sizes is introduced.
--   - encoding: P(A_0) = 1 - O(1/n). → One positive constant and threshold bound the complement probability by C/n.; reason: This expresses the asymptotic notation, without an exact probability equality.
--   - reading: Stage counts appear as fixed summation limits and deterministic factors outside expectations in section 5, although the interval widths are random. → A common pair of deterministic counts satisfies the actual stopping tests almost surely on the constructed virtual traces.; reason: This is the literal fixed-count reading of the printed formulas; nominal-width equalities are not assumed, and successful construction is asserted in the conclusion.
--   - encoding: Grid prices have indices j=1,...,κ_i. → Grid indices are j=0,...,k-1, with price lo+j(hi-lo)/k.; reason: The same left endpoints are enumerated; only the index origin changes.
--   - reading: The empirical argmax and argmin do not specify a tie rule. → Choose the least grid index attaining each finite optimum.; reason: This fixes an observable deterministic selection from the source argmax or argmin, without demand information.
--   - reading: The base-instance estimator is count/Δ and its inventory target is x/T. → For the size-n normalized instance, estimate base demand by count/(nΔ) and compare with x.; reason: Instantiating the pseudocode with inventory nx and dividing its rate estimate and target by n gives this rule; normalized time has horizon one.
-- source:
--   Wang, Deng, and Ye (2014), Operations Research 62(2), 318–331, DOI 10.1287/opre.2013.1245, Lemma 3, p. 325 (PDF 8)

import Definitions.Def_CloseGaps_DPA_RevenueEvents

open MeasureTheory Set

open scoped Classical

namespace CloseGaps.DPA

theorem lemma_3 (c : Coefficients) (hc : c.Positive) (x : ℝ) (hx : 0 < x) :
    ∃ C n₀ : ℝ, 0 < C ∧ 3 ≤ n₀ ∧
    ∀ a : Market, a.Valid → a.hi - a.lo = 1 →
    ∃ π : ℝ → PriceRule, ∀ n : ℝ, 3 ≤ n →
    ∀ lam : ℝ → ℝ, InClass c a x 1 lam →
    ∃ N : StageCounts, Experiment a lam n x (π n) N ∧
      (n₀ ≤ n → probability (A0 a lam n x N)ᶜ ≤ C / n) := by sorry

end CloseGaps.DPA
