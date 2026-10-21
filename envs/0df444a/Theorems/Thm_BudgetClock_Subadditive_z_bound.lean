-- Prove2me | Theorems.Thm_BudgetClock_Subadditive_z_bound
-- name    : BudgetClock.Subadditive.z_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:16.674984+00:00
-- url     : https://prove2.me/theorems/5070c382-e813-415c-a695-ad715f8e0cbd
-- title:
--   Proof of Theorem 8, p. 15 — a group Z of k bidders of cost ≤ B/k has v(Z) ≤ 4 · v(S_final)
-- statement:
--   Let $v \ge 0$ be a subadditive valuation on $n$ bidders, $c \ge 0$ a cost vector, $B > 0$ a budget, and $\mathrm{alg}$ a subroutine satisfying the 2-approximation guarantee of Mechanism 4. Let $F \in \mathbb{N}$ and let $Z \subseteq N$ be a set of $k = |Z|$ bidders with $1 \le k \le F$ and
--
--   $$c_i \le \frac{B}{k} \quad \text{for every } i \in Z.$$
--
--   Then the set $S_{\mathrm{final}}$ returned by Mechanism 4 run for at most $F$ phases satisfies
--
--   $$v(Z) \le 4 \, v(S_{\mathrm{final}}).$$
--
--   In the proof of Theorem 8 this is applied to each block $Z_i$ of the optimal set: every bidder of $Z_i$ stays active up to phase $|Z_i|$, where $v(Z_i) \le v(S_{\mathrm{prev}} \cap Z_i) + v(Z_i \setminus S_{\mathrm{prev}}) \le 2v(S_{\mathrm{prev}}) + 2v(S_{\mathrm{curr}}) \le 4\max\{v(S_{\mathrm{prev}}), v(S_{\mathrm{curr}})\}$, and the value of the output is at least that maximum.
--
--   **Formalization Note** The block $Z_i$ of the paper is replaced by any set $Z$ with the two properties the proof uses, $|Z| \ge 1$ and $c_i \le B/|Z|$ on $Z$; this avoids defining the blocks. The hypothesis $|Z| \le F$ ensures that phase $|Z|$ is reached unless the loop stops earlier; the statement covers an early stop as well.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 15, proof of Theorem 8, first case (display at the bottom of p. 15)

import Mathlib
import Definitions.Def_BudgetClock_Subadditive_Mechanism

namespace BudgetClock.Subadditive

theorem z_bound {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hsub : IsSubadditive v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) (halg : IsTwoApproxOracle v alg)
    (F : ℕ) (Z : Finset (Fin n)) (hZ : 1 ≤ Z.card) (hZF : Z.card ≤ F)
    (hZc : ∀ i ∈ Z, c i ≤ B / (Z.card : ℝ)) :
    v Z ≤ 4 * v (mechanism4 v c B alg F).1 := by sorry

end BudgetClock.Subadditive
