-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_Supplement_pure_equilibrium_np_complete
-- name    : CorrelatedAuctionComplexity.Main.Supplement.pure_equilibrium_np_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:45:44.945294+00:00
-- url     : https://prove2.me/theorems/cbface0b-7e71-4ec5-abe8-b4da8947d1d6
-- title:
--   Theorem 21 — NP-completeness of pure approximate HDFPA equilibrium existence
-- statement:
--   Let $N$ be the bit length of the canonical explicit description of a hypergraph discrete first-price auction. There exist positive integers $c,k$, independent of the auction and of the accuracy prescription, such that the following holds. For every polynomial-time evaluable rational prescription $\delta:\mathbb N\to\mathbb Q$ satisfying
--
--   $$0\le\delta(N)<\frac{1}{c(N+1)^k}\qquad\text{for every }N\in\mathbb N,$$
--
--   the decision language $L_\delta$ of normalized HDFPAs admitting a pure $\delta(N)$-approximate Nash equilibrium is NP-complete:
--
--   $$L_\delta\in\mathrm{NP}\quad\text{and}\quad\forall L\in\mathrm{NP},\quad L\le_{\mathrm p}L_\delta.$$
--
--   An HDFPA has finitely many bidders, explicit rational bids and values in $[0,1]$, and an explicit multiset of nonempty auctions with positive rational weights. Every bidder participates in some auction. Each bidder chooses one bid no larger than her value. Uniform tie-breaking determines first-price utility, and the allowed improvement for bidder $i$ is $\delta(N)W_i$, where $W_i$ is her total incident weight. There is no restriction on the finite bid set or on auction size. In particular, the identically zero prescription gives NP-completeness for exact pure equilibria.
--
--   This is the paper's independent companion theorem about existence of pure equilibria. It preserves both membership and hardness and does not assume an external hardness result or a supplied reduction. Theorem 1 remains the unchanged goal of the existing mission.
--
--   **Formalization Note** A polynomial-time machine must output the binary rational code of $\delta(|s|)$ on every binary input $s$. All mathematical profiles remain real; the purity predicate makes each bidder's lottery a single deterministic bid. The two positive threshold parameters are existential, and the added $1$ in $N+1$ makes the formula defined even at the empty string, which is not a well-formed auction code.
--
--   Differences from the source:
--
--   - reading: there exists an inverse-polynomial accuracy threshold in the description length → there exist positive integers c and k, chosen before all accuracy prescriptions, with threshold 1/(c*(N+1)^k); reason: makes the existential inverse-polynomial scale explicit without inventing a coefficient or exponent; N is the canonical binary description length
--   - reading: for all smaller approximation parameters epsilon-prime → for every polynomial-time evaluable rational prescription delta(N) with 0 <= delta(N) < 1/(c*(N+1)^k) for every N, including delta identically zero; reason: Definition 4 admits nonnegative error; the structured brief specifies effective length-dependent accuracies as the finite computational interpretation of the universal clause
--   - encoding: deciding whether an explicitly represented HDFPA has a pure approximate equilibrium → the language of canonical decodeH strings for WellFormed 1 HDFPAs on Fin n with a real profile satisfying Pure and IsNE, with non-codes excluded; reason: reuses the published binary rational auction codec and exact equilibrium predicates; pure real profiles are Dirac profiles and require no rational mixed-equilibrium assumption
--   - encoding: NP-complete → CookPvsNP.NPComplete over binary strings; reason: the published definition includes NP membership and actual polynomial-time many-one reductions from every NP language over every finite nonempty alphabet
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Theorem 21, p.28 (PDF p.28), proof p.29 (PDF p.29); standing assumptions Section 3.2, pp.10–11 (PDF pp.10–11), Definition 4.

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_Supplement_PureDecision

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main.Supplement

/-- Theorem 21, Appendix A, p.28 (proof p.29).
There is one positive reciprocal-polynomial threshold in the canonical auction bit
length such that every polynomial-time rational accuracy prescription strictly below
it, including the identically zero prescription, gives an NP-complete pure-equilibrium
existence decision language. No reduction or external hardness theorem is a hypothesis. -/
theorem pure_equilibrium_np_complete :
    ∃ c k : ℕ, 0 < c ∧ 0 < k ∧
      ∀ δ : ℕ → ℚ, PolynomialAccuracy δ →
        (∀ N : ℕ, 0 ≤ δ N ∧ δ N < reciprocalThreshold c k N) →
        CookPvsNP.NPComplete (pureExistenceLanguage δ) := by sorry

end CorrelatedAuctionComplexity.Main.Supplement
