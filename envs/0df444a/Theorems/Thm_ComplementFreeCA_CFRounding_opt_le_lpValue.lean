-- Prove2me | Theorems.Thm_ComplementFreeCA_CFRounding_opt_le_lpValue
-- name    : ComplementFreeCA.CFRounding.opt_le_lpValue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:14:07.732769+00:00
-- url     : https://prove2.me/theorems/f5d571b1-0f69-4ca1-98b9-1377a61ba1e1
-- title:
--   OPT* bounds OPT: the LP optimum is at least the welfare of every allocation
-- statement:
--   Let $v_1,\dots,v_n$ be valuations on the bundles of $M$ and let $x$ be an optimal solution of the LP relaxation, with value $OPT^*=\sum_{i,S}x_{i,S}v_i(S)$. Then for every allocation $(O_1,\dots,O_n)$ (pairwise disjoint bundles),
--   $$\sum_i v_i(O_i)\le OPT^*.$$
--   In particular $OPT^*$ is an upper bound on the optimal welfare $OPT$.
--
--   This is the first step of the proof of Theorem 3.1: every approximation guarantee relative to $OPT^*$ transfers to $OPT$.
--
--   **Formalization Note** No assumption on the valuations is needed; the statement is quantified over every allocation instead of naming an optimal one.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 6, §3.1, proof of Theorem 3.1, step (i), first sentence

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_ComplementFreeCA_CFRounding_LP

namespace ComplementFreeCA.CFRounding

theorem opt_le_lpValue {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsOptimalLP v x)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare v O ≤ lpValue v x := by sorry

end ComplementFreeCA.CFRounding
