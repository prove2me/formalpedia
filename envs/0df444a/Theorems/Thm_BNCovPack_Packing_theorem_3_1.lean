-- Prove2me | Theorems.Thm_BNCovPack_Packing_theorem_3_1
-- name    : BNCovPack.Packing.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:19:21.422983+00:00
-- url     : https://prove2.me/theorems/ef1acec4-d7be-4623-a679-f99e2ddb7104
-- title:
--   Theorem 3.1 — the online fractional packing scheme is $B$-competitive and violates each packing constraint by at most $2\log(1+n\,a_i(\max)/a_i(\min))/B$
-- statement:
--   Consider the **general online fractional packing problem**: $n\ge1$ packing constraints $\sum_k a(i,k)y(k)\le c(i)$ with known capacities $c(i)>0$, and $m\ge1$ variables $y(1),\dots,y(m)$ arriving online, the $j$-th together with its non-negative column $a(\cdot,j)$, each column having at least one positive entry; $y(j)$ may be set only in round $j$, and the objective is to maximize $\sum_k y(k)$. Run the online primal-dual scheme of Section 3 with parameter $B>0$.
--
--   **Theorem 3.1.** For any $B>0$:
--
--   1. the scheme's dual solution is non-negative, and the scheme is $B$-competitive: after every round $r\le m$, every $y'\ge 0$ satisfying the packing constraints restricted to the first $r$ columns, $\sum_{k\le r}a(i,k)y'(k)\le c(i)$ for all $i$, obeys
--   $$\sum_{k\le r}y'(k)\ \le\ B\sum_{k\le r}y(k);$$
--   2. after all $m$ rounds, for every packing constraint $i$,
--   $$\sum_{k=1}^{m}a(i,k)\,y(k)\ \le\ c(i)\cdot\frac{2\log\big(1+n\,a_i(\max)/a_i(\min)\big)}{B},$$
--   where $a_i(\max)=\max_k a(i,k)$ and $a_i(\min)=\min_k\{a(i,k)\mid a(i,k)\ne0\}$.
--
--   The paper writes the second bound as $c(i)\cdot O\big((\log n+\log(a_i(\max)/a_i(\min)))/B\big)$; the proof (claim (iii)) yields $c(i)\cdot 2\log(1+n\,a_i(\max)/a_i(\min))/B$. Choosing $B$ trades the competitive ratio against the constraint violation; scaling $y$ down by the violation factor gives a feasible packing solution that is $O(\log n+\log(a_{\max}/a_{\min}))$-competitive, which Lemma 3.1 of the paper shows is optimal up to constants.
--
--   **Formalization Note** The scheme is `stateAfter` of `BNCovPack.Packing.Scheme`, a deterministic function of the instance (the least $y(j)$ restoring the new covering constraint, as `sInf`). Competitiveness is stated against every feasible packing solution of each prefix of the input, since an online algorithm must be competitive at every time. Columns are `Fin m`, 0-based, so "$k\le r$" is `(k : ℕ) < r`. Logarithms are natural.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 5, Theorem 3.1 (explicit constant from the proof, claim (iii))

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance
import Definitions.Def_OnlinePrimalDual_GeneralPacking_aMax
import Definitions.Def_OnlinePrimalDual_GeneralPacking_aMin
import Definitions.Def_BNCovPack_Packing_Scheme

namespace BNCovPack.Packing

open OnlinePrimalDual.GeneralPacking

/-- Buchbinder–Naor 2009, Theorem 3.1 (p. 5). For any `B > 0`, the online fractional packing
scheme of §3 is `B`-competitive: after every round `r`, its dual solution `y` is non-negative and
every non-negative `y'` satisfying the packing constraints of the first `r` columns has value at
most `B` times the scheme's dual value. Moreover, after all `m` rounds, every packing constraint
`i` satisfies `∑_{k=1}^{m} a(i,k) y(k) ≤ c(i) · 2 log(1 + n aᵢ(max)/aᵢ(min)) / B` (the explicit
form of the paper's `c(i) · O((log n + log(aᵢ(max)/aᵢ(min)))/B)`, from claim (iii) of the proof). -/
theorem theorem_3_1 {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} [NeZero m]
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    (∀ r : ℕ, r ≤ m → ∀ k : Fin m, 0 ≤ (stateAfter inst B r).y k) ∧
    (∀ r : ℕ, r ≤ m → ∀ y' : Fin m → ℝ, (∀ k, 0 ≤ y' k) →
      (∀ i, ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < r), inst.a i k * y' k
        ≤ inst.c i) →
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < r), y' k ≤ B * dualValue inst B r) ∧
    (∀ i : I, ∑ k : Fin m, inst.a i k * (stateAfter inst B m).y k ≤
      inst.c i * (2 * Real.log (1 + (Fintype.card I : ℝ) * aMax inst i / aMin inst i)) / B) := by sorry

end BNCovPack.Packing
