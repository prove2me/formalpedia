-- Prove2me | Theorems.Thm_FBMSP_discrete_candidate_sufficiency
-- name    : FBMSP.discrete_candidate_sufficiency
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T11:46:04.495192+00:00
-- url     : https://prove2.me/theorems/8f2ef6ab-4b78-4205-8689-6a713787284d
-- title:
--   Appendix C — Finite candidate prices suffice
-- statement:
--   For a valid finite rational market with $n$ prediction values and $m$ error atoms, define
--   $$P=\{0\}\cup\{\mu_i+e_j:\mu_i+e_j\ge0\}.$$
--   Then every candidate is nonnegative, $|P|\le nm+1$, and every policy using arbitrary nonnegative real prices is weakly dominated by a policy using only prices from $P$, with the same customer assignment and at most the same number of price slots.
--
--   This is the finite-support link needed to apply the finite-candidate greedy guarantee to unrestricted pricing. The statement proves a cardinality bound; a machine-level cost of exact arithmetic is not asserted.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Appendix C, p.50 (ec16); Remark 3, p.18.

import Definitions.Def_FBMSP_DiscreteCandidates

namespace FBMSP

/-- Finite-support bridge for Remark 2 / Appendix C.  Every real-price policy
is dominated by a policy using realized nonnegative valuation breakpoints,
without changing its assignment.  Thus a finite-candidate optimization loses
no revenue in this discrete setting.  Draft statement; proof remains open.

The cardinality bound is explicit.  No computational runtime bound is
asserted here; exact-arithmetic evaluation costs require a separate model. -/
theorem discrete_candidate_sufficiency (I : RationalMarketInput)
    (hvalid : ValidRationalMarket I) :
    0 ∈ rationalCandidatePrices I ∧
    (∀ p ∈ rationalCandidatePrices I, 0 ≤ p) ∧
    (rationalCandidatePrices I).card ≤ I.means.length * I.shocks.length + 1 ∧
    ∀ (prices : Fin I.segments → ℝ)
      (assignment : Fin I.means.length → Fin I.segments),
      (∀ j, 0 ≤ prices j) →
      ∃ candidatePrices : Fin I.segments → ℝ,
        (∀ j, candidatePrices j ∈ rationalCandidatePrices I) ∧
        rationalMarketRevenue I prices assignment ≤
          rationalMarketRevenue I candidatePrices assignment := by sorry

end FBMSP
