-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_adversarial_regret_on_event
-- name    : BestBothWorlds.SAO.adversarial_regret_on_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:46:59.409625+00:00
-- url     : https://prove2.me/theorems/8092e862-3647-4629-9d07-6b98d7d597bb
-- title:
--   §4.3 — on the good event, $R_n\le60(1+\log K)(1+\log n)\sqrt{nK\log\beta+5K^2\log^2\beta}+200K^2\log^2\beta$
-- statement:
--   Let $K\ge2$, $n\ge K$, $\delta\in(0,1)$ and $\beta=10Kn^3\delta^{-1}$. Fix an adaptive adversary with rewards in $[0,1]$ and an arm path, and consider the run of SAO with parameter $\beta$. Suppose that:
--
--   1. (22) holds for every arm $i$ and every $t\in\{1,\dots,\tau_0\}$: $\big|\widetilde H_{i,t}-H_{i,t}\big|\le\sqrt{4\big(\frac{K\min(\tau_i,t)}{t^2}+\frac{\max(t-\tau_i,0)}{q_i\tau_i t}\big)\log\beta+5\big(\frac{K\log\beta}{\min(\tau_i,t)}\big)^2}$;
--   2. (24) holds for every arm $i$ and every $t\in\{1,\dots,\tau_0\}$: $T_i(t)\le q_i\tau_i(1+\log t)+\sqrt{4q_i\tau_i(1+\log t)\log\beta+5\log^2\beta}$;
--   3. (25) holds: $\max_i\sum_{t=\tau_0+1}^n g_{i,t}-\sum_{t=\tau_0+1}^n g_{I_t,t}\le5.15\sqrt{(n-\tau_0)K\log\beta}$.
--
--   Then
--   $$R_n\le60(1+\log K)(1+\log n)\sqrt{nK\log\beta+5K^2\log^2\beta}+200K^2\log^2\beta.$$
--
--   This is the deterministic half of the adversarial analysis. Combined with the adversarial union event, it gives the adversarial part of Theorem 4.1.
--
--   **Formalization Note** The last line of the paper's chain (p. 19) has $K^2\log^2\beta$ under the root. The statement here uses $5K^2\log^2\beta$, as in Theorem 4.1 (p. 12). This is weaker, so it follows from the paper's chain.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, pp. 18–19, §4.3 (final chain); constant as in Theorem 4.1, p. 12

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- §4.3 (pp. 18–19): on a run of SAO with `β = 10Kn³δ⁻¹` against an adaptive adversary with
rewards in `[0,1]` along which (22) and (24) hold for every arm `i` and every time
`t ∈ {1, …, τ₀}`, and (25) holds,
`R_n ≤ 60 (1 + log K)(1 + log n) √(nK log β + 5K² log² β) + 200 K² log² β`. -/
theorem adversarial_regret_on_event (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (adv : Adversary K) (hadv : adv.IsBounded)
    (I : Fin n → Fin K)
    (h22 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I),
      |estAvg (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) adv I i t - fixedAvg adv I i t| ≤
        estRadius K (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) t (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)))
    (h24 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I),
      (pullCount I i t : ℝ) ≤
        pullBound (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) t (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)))
    (h25 : regretFrom adv I (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I) ≤
      5.15 * Real.sqrt (((n : ℝ) - tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I) * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ))) :
    regret adv I ≤
      60 * (1 + Real.log K) * (1 + Real.log n) *
          Real.sqrt (n * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) + 5 * K ^ 2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2) +
        200 * K ^ 2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2 := by sorry

end BestBothWorlds.SAO
