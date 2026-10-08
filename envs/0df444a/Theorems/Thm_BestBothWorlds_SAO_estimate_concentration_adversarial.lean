-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_estimate_concentration_adversarial
-- name    : BestBothWorlds.SAO.estimate_concentration_adversarial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:47:10.427987+00:00
-- url     : https://prove2.me/theorems/9236924e-dcea-4dbe-b092-a0d299cb0b42
-- title:
--   Lemma 4.5 (adversarial model) — concentration of $\widetilde H_{i,t}$ around $H_{i,t}$
-- statement:
--   Consider SAO with parameter $\beta>1$ on $K\ge2$ arms and $n\ge K$ rounds against an adaptive adversary with rewards in $[0,1]$. Fix an arm $i$, a time $t\in\{1,\dots,n\}$ and $\delta>0$. With $\tau_0$, $\tau_i\leftarrow\min(\tau_i,\tau_0)$ and $q_i=p_{i,\min(\tau_i,\tau_0)}$ as in §4, with probability at least $1-\delta$, if $t\le\tau_0$ then
--   $$\big|\widetilde H_{i,t}-H_{i,t}\big|\le\sqrt{4\Big(\frac{K\min(\tau_i,t)}{t^2}+\frac{\max(t-\tau_i,0)}{q_i\tau_i t}\Big)\log(2t^2\delta^{-1})+5\Big(\frac{K\log(2t^2\delta^{-1})}{\min(\tau_i,t)}\Big)^2}.$$
--   Here $H_{i,t}=\frac1t\sum_{s\le t}g_{i,s}$ is the average reward of arm $i$, computed with the rewards the adversary produces along the run.
--
--   This is the adversarial counterpart of the stochastic part and the source of (22).
--
--   **Formalization Note** The event is "$t\le\tau_0$ implies the bound" for one fixed pair $(i,t)$.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 15, Lemma 4.5 (second display)

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- Lemma 4.5, adversarial part (p. 15): for a fixed arm `i` and time `t`, against any adaptive
adversary with rewards in `[0,1]`, with probability at least `1 - δ`, if `t ≤ τ₀` then
`|H̃_{i,t} - H_{i,t}| ≤ √(4 (K min(τ_i,t)/t² + max(t-τ_i,0)/(q_i τ_i t)) log(2t²δ⁻¹)
  + 5 (K log(2t²δ⁻¹)/min(τ_i,t))²)`. -/
theorem estimate_concentration_adversarial (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (β : ℝ)
    (hβ : 1 < β) (adv : Adversary K) (hadv : adv.IsBounded) (i : Fin K) (t : ℕ) (ht : 1 ≤ t)
    (htn : t ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ probEvent n (sao K n β) adv (fun I =>
      t ≤ tau0 K n β adv I →
        |estAvg (sao K n β) adv I i t - fixedAvg adv I i t| ≤
          estRadius K (tauEff K n β adv I i) (qEff K n β adv I i) t
            (Real.log (2 * (t : ℝ) ^ 2 / δ))) := by sorry

end BestBothWorlds.SAO
