-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_aps_to_mrv
-- name    : ApproxPolySatCH.Main.aps_to_mrv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:12:51.968818+00:00
-- url     : https://prove2.me/theorems/fef3aac5-283c-4e73-bed9-f7f7abb9f321
-- title:
--   Theorem 2 — Randomized APS to MRV Turing reduction
-- statement:
--   There is a randomized polynomial-time Turing reduction over the rationals, and for every finite coefficient field k there is such a reduction to the uniform finite-field MRV language:
--   $$\mathrm{APS}_{\mathbb Q}\le_T^{\mathrm{BPP}}\mathrm{MRV}_{\mathbb Q},\qquad\mathrm{APS}_k\le_T^{\mathrm{BPP}}\mathrm{MRV}_{\mathrm{fin}}.$$
--   Every finite-field oracle query includes its coefficient-field description and uses a finite extension of the original k, with an actual embedding and extension degree bounded by one polynomial in the original binary input length. Finite machine descriptions, clocks and seed-length polynomials are quantified before every input. All branches halt, query construction is charged, and the two-sided error is at most $1/3$.
--
--   This asserts the complete reduction, rather than an algebraic criterion conditional on a free coefficient oracle.
--
--   Differences from the source:
--   - encoding: Randomized polynomial-time Turing reductions and polynomial-degree finite extensions in every finite-field query. → Finite machines with all branches clocked, at most one-third two-sided error, and actual query-tape words with supplied field descriptions and bounded extension degrees.; reason: This is the ordinary bit-cost reduction assertion; no expanded resultant or coefficient-access operation is made free.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Theorem 2, p.23 (PDF p.23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=23

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem aps_to_mrv :
    RandomizedTuringReduction (SparseLanguage .rational) (MRV .rational) ∧
    ∀ k : CoefficientField, k ≠ .rational →
      ∃ (M : NKtLB.Machine) (c d a b e h : ℕ),
        RandomizedDecider M MRVFinite (SparseLanguage k) c d a b ∧
        QueryExtensions k M c d a b e h := by sorry

end ApproxPolySatCH.Main
