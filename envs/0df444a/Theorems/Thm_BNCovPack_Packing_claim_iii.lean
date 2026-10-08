-- Prove2me | Theorems.Thm_BNCovPack_Packing_claim_iii
-- name    : BNCovPack.Packing.claim_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:19:31.00599+00:00
-- url     : https://prove2.me/theorems/688b2791-393a-4b82-bf76-a64f6c3d8f23
-- title:
--   Theorem 3.1, proof, claim (iii) — each packing constraint is violated by at most $2\log(1+n\,a_i(\max)/a_i(\min))/B$
-- statement:
--   Consider the online fractional packing scheme of Section 3 with parameter $B>0$, run on an instance with $n\ge 1$ primal variables, $m\ge 1$ columns, costs $c(i)>0$, non-negative coefficients $a(i,k)$, and every column having at least one positive entry. For a packing constraint $i$ let
--   $$a_i(\max)=\max_{1\le k\le m}a(i,k),\qquad a_i(\min)=\min_{1\le k\le m}\{a(i,k)\mid a(i,k)\neq 0\}.$$
--   Then the final dual solution $y$ satisfies, for every $i$,
--   $$\sum_{k=1}^{m}a(i,k)\,y(k)\ \le\ c(i)\cdot\frac{2\log\big(1+n\,a_i(\max)/a_i(\min)\big)}{B}.$$
--
--   The paper writes the conclusion of Theorem 3.1 as $c(i)\cdot O\big((\log n+\log(a_i(\max)/a_i(\min)))/B\big)$; this is the explicit bound its proof establishes. It says the scheme's dual solution violates each packing constraint by at most a logarithmic factor divided by $B$.
--
--   **Formalization Note** $a_i(\max)$ and $a_i(\min)$ are the published `aMax` and `aMin`, taken over all $m$ columns (unlike the prefix maximum used inside the scheme). When row $i$ has no non-zero coefficient, `aMin` is $0$, the Lean expression $n\cdot 0/0$ is $0$, and both sides are $0$. The logarithm is natural (`Real.log`).
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 5, Theorem 3.1, proof, claim (iii) (proved p. 6)

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance
import Definitions.Def_OnlinePrimalDual_GeneralPacking_aMax
import Definitions.Def_OnlinePrimalDual_GeneralPacking_aMin
import Definitions.Def_BNCovPack_Packing_Scheme

namespace BNCovPack.Packing

open OnlinePrimalDual.GeneralPacking

/-- Buchbinder–Naor 2009, proof of Theorem 3.1, claim (iii) (p. 5; proved p. 6): when the scheme
has processed all `m` columns, every packing constraint `i` is violated by at most a factor
`2 log(1 + n aᵢ(max)/aᵢ(min))/B`:
`∑_{k=1}^{m} a(i,k) y(k) ≤ c(i) · 2 log(1 + n aᵢ(max)/aᵢ(min)) / B`,
with `n = |I|`, `aᵢ(max)` the largest and `aᵢ(min)` the smallest non-zero coefficient of `x(i)`
over all `m` columns, and the natural logarithm. -/
theorem claim_iii {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} [NeZero m]
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    ∀ i : I, ∑ k : Fin m, inst.a i k * (stateAfter inst B m).y k ≤
      inst.c i * (2 * Real.log (1 + (Fintype.card I : ℝ) * aMax inst i / aMin inst i)) / B := by sorry

end BNCovPack.Packing
