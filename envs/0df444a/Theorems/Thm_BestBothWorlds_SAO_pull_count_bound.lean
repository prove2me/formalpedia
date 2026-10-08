-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_pull_count_bound
-- name    : BestBothWorlds.SAO.pull_count_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:46:12.671843+00:00
-- url     : https://prove2.me/theorems/925e7ff2-ad04-48ff-b1e1-22f78022c732
-- title:
--   Lemma 4.7 — the number of plays $T_i(t)$ is at most $q_i\tau_i(1+\log t)$ plus a deviation term
-- statement:
--   Consider SAO with parameter $\beta>1$ on $K\ge2$ arms and $n\ge K$ rounds against an adaptive adversary with rewards in $[0,1]$. Every reward table of the stochastic model is such an adversary, so the statement covers both models. Fix an arm $i$, a time $t\in\{1,\dots,n\}$ and $\delta>0$. With $\tau_0$, $\tau_i\leftarrow\min(\tau_i,\tau_0)$ and $q_i=p_{i,\min(\tau_i,\tau_0)}$ as in §4, with probability at least $1-\delta$, if $t\le\tau_0$ then
--   $$T_i(t)\le q_i\tau_i(1+\log t)+\sqrt{4q_i\tau_i(1+\log t)\log(t\delta^{-1})+5\log^2(t\delta^{-1})}.$$
--
--   After deactivation the probability of arm $i$ decays like $q_i\tau_i/s$, so the expected number of plays up to $t$ is at most $q_i\tau_i(1+\log t)$. This lemma controls the deviation from that expectation and gives (24).
--
--   **Formalization Note** The event is "$t\le\tau_0$ implies the bound" for one fixed pair $(i,t)$. The stochastic model follows by integrating over reward tables.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 16, Lemma 4.7

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- Lemma 4.7 (p. 16): for a fixed arm `i` and time `t`, against any adaptive adversary with
rewards in `[0,1]` (this covers every reward table of the stochastic model), with probability at
least `1 - δ`, if `t ≤ τ₀` then
`T_i(t) ≤ q_i τ_i (1 + log t) + √(4 q_i τ_i (1 + log t) log(tδ⁻¹) + 5 log²(tδ⁻¹))`. -/
theorem pull_count_bound (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (β : ℝ) (hβ : 1 < β)
    (adv : Adversary K) (hadv : adv.IsBounded) (i : Fin K) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ probEvent n (sao K n β) adv (fun I =>
      t ≤ tau0 K n β adv I →
        (pullCount I i t : ℝ) ≤
          pullBound (qEff K n β adv I i) (tauEff K n β adv I i) t (Real.log (t / δ))) := by sorry

end BestBothWorlds.SAO
