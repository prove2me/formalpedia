-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_union_event_adversarial
-- name    : BestBothWorlds.SAO.union_event_adversarial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:46:37.738873+00:00
-- url     : https://prove2.me/theorems/169808da-9b40-4d16-9d15-66c3c209d373
-- title:
--   §4.1, (22), (24), (25) — the good event in the adversarial model
-- statement:
--   Let $K\ge2$, $n\ge K$, $\delta\in(0,1)$ and $\beta=10Kn^3\delta^{-1}$. Consider SAO with parameter $\beta$ against an adaptive adversary with rewards in $[0,1]$. With probability at least $1-\delta$:
--
--   1. (22) for every arm $i$ and every time $t\in\{1,\dots,\tau_0\}$, $\displaystyle\big|\widetilde H_{i,t}-H_{i,t}\big|\le\sqrt{4\Big(\frac{K\min(\tau_i,t)}{t^2}+\frac{\max(t-\tau_i,0)}{q_i\tau_i t}\Big)\log\beta+5\Big(\frac{K\log\beta}{\min(\tau_i,t)}\Big)^2}$;
--   2. (24) for every arm $i$ and every time $t\in\{1,\dots,\tau_0\}$, $T_i(t)\le q_i\tau_i(1+\log t)+\sqrt{4q_i\tau_i(1+\log t)\log\beta+5\log^2\beta}$;
--   3. (25) $\displaystyle\max_{i}\sum_{t=\tau_0+1}^n g_{i,t}-\sum_{t=\tau_0+1}^n g_{I_t,t}\le5.15\sqrt{(n-\tau_0)K\log\beta}$.
--
--   This collects Lemmas 4.5, 4.7 and 4.8 by a union bound. The deterministic analysis of §4.3 runs on this event.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 17, §4.1, eq. (22), (24), (25)

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- §4.1, (22), (24), (25) (p. 17), adversarial model: with `β = 10Kn³δ⁻¹`, against any adaptive
adversary with rewards in `[0,1]`, with probability at least `1 - δ`: for every arm `i` and every
time `t ∈ {1, …, τ₀}`,
(22) `|H̃_{i,t} - H_{i,t}| ≤ √(4 (K min(τ_i,t)/t² + max(t-τ_i,0)/(q_i τ_i t)) log β
  + 5 (K log β/min(τ_i,t))²)` and
(24) `T_i(t) ≤ q_i τ_i (1 + log t) + √(4 q_i τ_i (1 + log t) log β + 5 log² β)`; and
(25) `max_i ∑_{t=τ₀+1}^n g_{i,t} - ∑_{t=τ₀+1}^n g_{I_t,t} ≤ 5.15 √((n - τ₀) K log β)`. -/
theorem union_event_adversarial (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (adv : Adversary K) (hadv : adv.IsBounded) :
    1 - δ ≤ probEvent n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) adv (fun I =>
      (∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I),
        |estAvg (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) adv I i t - fixedAvg adv I i t| ≤
            estRadius K (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) t
              (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ∧
        (pullCount I i t : ℝ) ≤
            pullBound (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) t
              (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ))) ∧
      regretFrom adv I (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I) ≤
        5.15 * Real.sqrt (((n : ℝ) - tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I) * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ))) := by sorry

end BestBothWorlds.SAO
