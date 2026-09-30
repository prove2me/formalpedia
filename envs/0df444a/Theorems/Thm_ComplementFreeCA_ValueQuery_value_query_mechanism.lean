-- Prove2me | Theorems.Thm_ComplementFreeCA_ValueQuery_value_query_mechanism
-- name    : ComplementFreeCA.ValueQuery.value_query_mechanism
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:58:01.044988+00:00
-- url     : https://prove2.me/theorems/e7f55fd7-1732-4899-89bf-3cec39c31f99
-- title:
--   Theorem 5.1 — a maximal-in-range value-query mechanism is truthful and a 2√m-approximation for complement-free bidders
-- statement:
--   Let $n$ bidders with valuations on bundles of $M=\{1,\dots,m\}$ take part in the following mechanism (§5.2). On the report profile $b$: compute a maximum-weight matching $P$ in the complete bipartite graph between items and bidders with edge costs $b_i(\{j\})$, and a bidder $t$ maximizing $b_i(M)$; if $b_t(M)$ is strictly higher than the weight $|P|$, allocate all items to $t$, otherwise give each item matched by $P$ to its matched bidder. Each bidder $i$ receives the VCG payment $\sum_{k\ne i} b_k(\mathrm{ALG}(b)_k)$.
--
--   For every way of choosing the maximum-weight matching and the top bidder as functions of the reports:
--
--   1. **Approximation.** For every profile $v=(v_1,\dots,v_n)$ of normalized, monotone, complement-free valuations and every allocation $O$ (pairwise disjoint bundles),
--   $$\sum_{i=1}^n v_i(O_i)\;\le\;2\sqrt m\,\sum_{i=1}^n v_i\big(\mathrm{ALG}(v)_i\big).$$
--   2. **Incentive compatibility.** On the domain of normalized, monotone, complement-free valuations, reporting the true valuation is a dominant strategy: for every such profile $v$, every bidder $i$ and every such misreport $v_i'$, bidder $i$'s utility $v_i(\mathrm{ALG}(\cdot)_i)$ plus payment under $(v_i,v_{-i})$ is at least its utility under $(v_i',v_{-i})$.
--
--   The algorithm uses value queries only ($b_i(M)$ and $b_i(\{j\})$), and the result shows that a $\sqrt m$-order approximation for complement-free bidders is achievable truthfully in the value-query model.
--
--   **Formalization Note** The paper writes $O(\sqrt m)$; its proof yields the ratio $2\sqrt m$ (both cases end with a welfare of at least $|OPT|/(2\sqrt m)$, pp. 11–12), which is stated here. "In polynomial time" is a running-time claim and is not formalized. The matching and the top bidder are function parameters of the reports with specification hypotheses, so the statement covers every tie-breaking. The paper's "the optimal allocation" is strengthened to every allocation $O$. The mechanism pays the bidders (the paper's convention, footnote 2). At $m=0$ the approximation holds trivially; with $n=0$ no top-bidder rule exists and the statement is vacuous, as is the auction.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 11, Theorem 5.1 (with §5.1 and §5.2 steps (i)–(iii)); proof pp. 11–12

import Mathlib
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic

open Finset

namespace ComplementFreeCA.ValueQuery

/-- Theorem 5.1 (p. 11): with complement-free valuations, the algorithm of §5.2 is a
`2√m`-approximation (the paper writes `O(√m)`) and, with the VCG payments of §5.1, is
incentive compatible on the CF valuations; for every maximum-weight matching rule and every
top-bidder rule. -/
theorem value_query_mechanism {n m : ℕ}
    (mat : (Fin n → Finset (Fin m) → ℝ) → Fin m → Option (Fin n))
    (top : (Fin n → Finset (Fin m) → ℝ) → Fin n)
    (hmat : IsMaxWeightMatchingRule mat) (htop : IsTopBidderRule top) :
    (∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, IsCFValuation (v i)) →
      ∀ O : Fin n → Finset (Fin m), IsAllocation O →
        welfare v O ≤ 2 * Real.sqrt m * welfare v (alg mat top v)) ∧
    IncentiveCompatibleOn IsCFValuation (alg mat top) := by sorry

end ComplementFreeCA.ValueQuery
