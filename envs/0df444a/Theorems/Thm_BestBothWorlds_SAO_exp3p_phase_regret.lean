-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_exp3p_phase_regret
-- name    : BestBothWorlds.SAO.exp3p_phase_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:46:29.905681+00:00
-- url     : https://prove2.me/theorems/55803a07-922a-4dbd-ac9e-6f85465e162d
-- title:
--   Lemma 4.8 — regret of the Exp3.P phase, at most $5.15\sqrt{(n-\tau_0)K\log(K\delta^{-1})}$
-- statement:
--   Let $K\ge2$, $n\ge K$ and $\delta\in(0,1)$. Run SAO with parameter $\beta=K/\delta$, so that the Exp3.P it starts after round $\tau_0$ is tuned for confidence $\delta$ and horizon $n-\tau_0$. Then against every adaptive adversary with rewards in $[0,1]$, with probability at least $1-\delta$,
--   $$\max_{i\in\{1,\dots,K\}}\sum_{t=\tau_0+1}^n g_{i,t}-\sum_{t=\tau_0+1}^n g_{I_t,t}\le5.15\sqrt{(n-\tau_0)K\log(K\delta^{-1})}.$$
--
--   This is the high-probability guarantee of Exp3.P (Bubeck–Cesa-Bianchi 2012, Theorem 3.2, eq. (3.10)), applied to the rounds after the switch. With $\delta=K/\beta$ it gives (25).
--
--   **Formalization Note** The paper leaves Exp3.P's confidence parameter implicit. This mission fixes it at $\delta_P=K/\beta$, so Lemma 4.8 with confidence $\delta$ concerns SAO with $\beta=K/\delta$. If Exp3.P is never started ($\tau_0=n$), both sides are $0$.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 17, Lemma 4.8; Bubeck & Cesa-Bianchi 2012, Theorem 3.2, eq. (3.10)

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- Lemma 4.8 (p. 17): the Exp3.P phase. SAO with parameter `β = K/δ` starts Exp3.P with
confidence `δ`; against any adaptive adversary with rewards in `[0,1]`, with probability at least
`1 - δ`, `max_i ∑_{t=τ₀+1}^n g_{i,t} - ∑_{t=τ₀+1}^n g_{I_t,t} ≤ 5.15 √((n - τ₀) K log(Kδ⁻¹))`. -/
theorem exp3p_phase_regret (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (adv : Adversary K) (hadv : adv.IsBounded) :
    1 - δ ≤ probEvent n (sao K n (K / δ)) adv (fun I =>
      regretFrom adv I (tau0 K n (K / δ) adv I) ≤
        5.15 * Real.sqrt (((n : ℝ) - tau0 K n (K / δ) adv I) * K * Real.log (K / δ))) := by sorry

end BestBothWorlds.SAO
