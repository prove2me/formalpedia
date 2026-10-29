-- Prove2me | Theorems.Thm_CloseGaps_DPA_lemma_4
-- name    : CloseGaps.DPA.lemma_4
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:36:11.953816+00:00
-- url     : https://prove2.me/theorems/b0b3441e-0926-4f83-ad84-edc59c8d90ec
-- title:
--   Lemma 4 — Step 2 revenue; equation (29)
-- statement:
--   Lemma 4.
--   E[∑_{i=1}^{N^u} ∑_{j=1}^{κ_i^u} p_{i,j}^u Y_{ij}^u
--     I(⋃_{l=i}^{N^u+1} B_l) I(A_1)]
--   ≥ ∑_{i=1}^{N^u} nτ_i^u p^D λ(p^D) P(⋃_{l=i}^{N^u+1} B_i)
--     − Cnτ_1^u log n.                                             (29)
--
--   Differences from the source:
--   - encoding: Continuous-time controlled Poisson sales with an off action. → A measurable price rule on sale histories, exponential interarrivals and Option-valued actions.; reason: The off action has zero intensity and revenue; the history rule cannot access the unknown demand.
--   - reading: The size parameter n is written without an integrality restriction. → n is real.; reason: This retains the displayed domain, including every integer size.
--   - encoding: The DPA objects are constructed by the displayed algorithm. → Partial stage construction and successful construction in the conclusion.; reason: Definedness is asserted in the conclusion at the source sizes: every printed real grid count must be an exact positive integer, each stage duration positive, and each stopping minimum attained; no rounding or restriction to executable sizes is introduced.
--   - reading: Stage counts appear as fixed summation limits and deterministic factors outside expectations in section 5, although the interval widths are random. → A common pair of deterministic counts satisfies the actual stopping tests almost surely on the constructed virtual traces.; reason: This is the literal fixed-count reading of the printed formulas; nominal-width equalities are not assumed, and successful construction is asserted in the conclusion.
--   - encoding: Grid prices have indices j=1,...,κ_i. → Grid indices are j=0,...,k-1, with price lo+j(hi-lo)/k.; reason: The same left endpoints are enumerated; only the index origin changes.
--   - reading: The empirical argmax and argmin do not specify a tie rule. → Choose the least grid index attaining each finite optimum.; reason: This fixes an observable deterministic selection from the source argmax or argmin, without demand information.
--   - reading: The base-instance estimator is count/Δ and its inventory target is x/T. → For the size-n normalized instance, estimate base demand by count/(nΔ) and compare with x.; reason: Instantiating the pseudocode with inventory nx and dividing its rate estimate and target by n gives this rule; normalized time has horizon one.
-- source:
--   Wang, Deng, and Ye (2014), Operations Research 62(2), 318–331, DOI 10.1287/opre.2013.1245, Lemma 4, p. 325 (PDF 8)

import Definitions.Def_CloseGaps_DPA_RevenueEvents

open MeasureTheory Set

open scoped Classical

namespace CloseGaps.DPA

theorem lemma_4 (c : Coefficients) (hc : c.Positive) (x : ℝ) (hx : 0 < x) :
    ∃ C : ℝ, 0 < C ∧
    ∀ a : Market, a.Valid → a.hi - a.lo = 1 →
    ∃ π : ℝ → PriceRule, ∀ n : ℝ, 3 ≤ n →
    ∀ lam : ℝ → ℝ, InClass c a x 1 lam →
    ∃ N : StageCounts, Experiment a lam n x (π n) N ∧
      (∑ i ∈ Finset.Icc 1 N.Nu,
        n * tauU n i * dOpt a x 1 lam * lam (dOpt a x 1 lam) *
          probability (⋃ (_l : ℕ) (_h : _l ∈ Icc i (N.Nu + 1)), B a lam n x N i)) -
        C * n * tauU n 1 * Real.log n ≤ ∫ E, revenue4 a lam n x N E ∂clockLaw := by sorry

end CloseGaps.DPA
