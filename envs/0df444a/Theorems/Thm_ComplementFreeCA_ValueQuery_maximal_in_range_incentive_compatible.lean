-- Prove2me | Theorems.Thm_ComplementFreeCA_ValueQuery_maximal_in_range_incentive_compatible
-- name    : ComplementFreeCA.ValueQuery.maximal_in_range_incentive_compatible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:55:14.057993+00:00
-- url     : https://prove2.me/theorems/bd88ca64-3ae1-463f-90b0-82d880dca8b1
-- title:
--   §5.1 — a maximal-in-range allocation rule with VCG payments is incentive compatible
-- statement:
--   Let $D$ be a set of valuations on bundles of $M=\{1,\dots,m\}$, let $R$ be a set of allocations to $n$ bidders, and let $f$ be an allocation rule mapping report profiles to allocations. Suppose $f$ is **maximal in range** with range $R$ on $D$: for every report profile $b=(b_1,\dots,b_n)$ with each $b_k\in D$, the allocation $f(b)$ lies in $R$ and
--   $$\sum_{i} b_i\big(a_i\big)\;\le\;\sum_i b_i\big(f(b)_i\big)\qquad\text{for all } a\in R.$$
--   Pay every bidder $i$ the sum $\sum_{k\ne i} b_k(f(b)_k)$ of the other bidders' reported values (the VCG payment scheme). Then the mechanism is **incentive compatible** on $D$: for every profile $v$ with each $v_k\in D$, every bidder $i$ and every $v_i'\in D$,
--   $$v_i\big(f(v_i',v_{-i})_i\big)+\sum_{k\ne i} v_k\big(f(v_i',v_{-i})_k\big)\;\le\;v_i\big(f(v)_i\big)+\sum_{k\ne i} v_k\big(f(v)_k\big).$$
--
--   This is the observation of §5.1 that makes every maximal-in-range algorithm truthful: a bidder's utility equals the true welfare of the chosen allocation, which truthful reporting maximizes over the range.
--
--   **Formalization Note** No property of $D$ or $R$ is assumed; the domain enters only through the quantification over report profiles.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 11, §5.1, paragraph 'An algorithm is maximal in range …'

import Mathlib
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic

open Finset

namespace ComplementFreeCA.ValueQuery

/-- §5.1 (p. 11): a maximal-in-range allocation rule with the VCG payments is incentive
compatible on the same valuation domain. -/
theorem maximal_in_range_incentive_compatible {n m : ℕ}
    (D : (Finset (Fin m) → ℝ) → Prop) (R : Set (Fin n → Finset (Fin m)))
    (f : (Fin n → Finset (Fin m) → ℝ) → Fin n → Finset (Fin m))
    (hf : IsMaximalInRange D R f) :
    IncentiveCompatibleOn D f := by sorry

end ComplementFreeCA.ValueQuery
