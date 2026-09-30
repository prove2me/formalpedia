-- Prove2me | Theorems.Thm_ComplementFreeCA_XOSRounding_lp_optimum_ge_welfare
-- name    : ComplementFreeCA.XOSRounding.lp_optimum_ge_welfare
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:21:34.016451+00:00
-- url     : https://prove2.me/theorems/52d5e79d-4bd4-401e-b389-22c4b8d7e9ba
-- title:
--   The optimal fractional value $OPT^*$ bounds the welfare of every allocation
-- statement:
--   Let $v_1,\dots,v_n$ be valuations on the bundles of $M=\{1,\dots,m\}$ and let $x$ be an optimal solution of the LP relaxation, with value $\mathrm{OPT}^*=\sum_{i,S}x_{i,S}v_i(S)$. Then for every allocation $(O_1,\dots,O_n)$ (pairwise disjoint bundles),
--   $$\sum_{i} v_i(O_i)\ \le\ \mathrm{OPT}^*.$$
--   In particular the optimal fractional value is an upper bound on the value $\mathrm{OPT}$ of the optimal integral allocation.
--
--   This is the first link in the chain of the approximation guarantee: the rounding algorithm is compared with $\mathrm{OPT}^*$, and this inequality transfers the guarantee to the integral optimum.
--
--   **Formalization Note** No property of the valuations is needed. The paper states this fact without a label in step (i) of the proof of Theorem 3.1 and uses it again for Theorem 3.2.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 6, §3.1, proof of Theorem 3.1, step (i), first sentence

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSRounding_Model

namespace ComplementFreeCA.XOSRounding

theorem lp_optimum_ge_welfare {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPOptimal v x)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare v O ≤ lpValue v x := by sorry

end ComplementFreeCA.XOSRounding
