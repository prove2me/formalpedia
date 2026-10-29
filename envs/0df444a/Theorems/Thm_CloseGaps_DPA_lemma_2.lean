-- Prove2me | Theorems.Thm_CloseGaps_DPA_lemma_2
-- name    : CloseGaps.DPA.lemma_2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:35:44.431475+00:00
-- url     : https://prove2.me/theorems/79a32c6d-6eb4-454b-89f5-360108e9cbae
-- title:
--   Lemma 2 — Iteration bound
-- statement:
--   Lemma 2. max{N^u,N^c} ≤ 3 log n for n ≥ 3.
--
--   Differences from the source:
--   - encoding: Stage counts in equations (17) and (21). → Existence of a complete trace and counts satisfying the minimum tests.; reason: Definedness is asserted in the conclusion at the source sizes: every printed real grid count must be an exact positive integer, each stage duration positive, and each stopping minimum attained; no rounding or restriction to executable sizes is introduced.
--   - reading: Stage counts appear as fixed summation limits and deterministic factors outside expectations in section 5, although the interval widths are random. → A common pair of deterministic counts satisfies the actual stopping tests almost surely on the constructed virtual traces.; reason: This is the literal fixed-count reading of the printed formulas; nominal-width equalities are not assumed, and successful construction is asserted in the conclusion.
--   - reading: The size parameter has no explicit integrality restriction. → n is real with n ≥ 3.; reason: This retains every stated size, including all integer sizes.
--   - encoding: Grid prices have indices j=1,...,κ_i. → Grid indices are j=0,...,k-1, with price lo+j(hi-lo)/k.; reason: The same left endpoints are enumerated; only the index origin changes.
--   - reading: The empirical argmax and argmin do not specify a tie rule. → Choose the least grid index attaining each finite optimum.; reason: This fixes an observable deterministic selection from the source argmax or argmin, without demand information.
--   - reading: The base-instance estimator is count/Δ and its inventory target is x/T. → For the size-n normalized instance, estimate base demand by count/(nΔ) and compare with x.; reason: Instantiating the pseudocode with inventory nx and dividing its rate estimate and target by n gives this rule; normalized time has horizon one.
-- source:
--   Wang, Deng, and Ye (2014), Operations Research 62(2), 318–331, DOI 10.1287/opre.2013.1245, Lemma 2, p. 324 (PDF 7)

import Definitions.Def_CloseGaps_DPA_RevenueEvents

open MeasureTheory Set

open scoped Classical

namespace CloseGaps.DPA

theorem lemma_2 (c : Coefficients) (hc : c.Positive) (x : ℝ) (hx : 0 < x)
    (a : Market) (ha : a.Valid) (hw : a.hi - a.lo = 1)
    (lam : ℝ → ℝ) (hlam : InClass c a x 1 lam) (n : ℝ) (hn : 3 ≤ n) :
    ∃ N : StageCounts, (∀ᵐ E ∂clockLaw, completeTrace a lam n x N E) ∧
      (max N.Nu N.Nc : ℝ) ≤ 3 * Real.log n := by sorry

end CloseGaps.DPA
