-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_union_event_stochastic
-- name    : BestBothWorlds.SAO.union_event_stochastic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:46:25.742808+00:00
-- url     : https://prove2.me/theorems/a12151c4-0274-4b50-a2bb-b77f62348123
-- title:
--   §4.1, (21), (23), (24) — the good event in the stochastic model
-- statement:
--   Let $K\ge2$, $n\ge K$, $\delta\in(0,1)$ and $\beta=10Kn^3\delta^{-1}$. Consider SAO with parameter $\beta$ in the stochastic model with distributions $\nu_1,\dots,\nu_K$ on $[0,1]$ and means $\mu_i$. With probability at least $1-\delta$, the following hold for every arm $i$ and every time $t\in\{1,\dots,\tau_0\}$:
--
--   1. (21) $\displaystyle\big|\widetilde H_{i,t}-\mu_i\big|\le\sqrt{4\Big(\frac{K\min(\tau_i,t)}{t^2}+\frac{\max(t-\tau_i,0)}{q_i\tau_i t}\Big)\log\beta+5\Big(\frac{K\log\beta}{\min(\tau_i,t)}\Big)^2}$;
--   2. (23) if $T_i(t)\ge1$, then $\displaystyle\big|\widehat H_{i,t}-\mu_i\big|\le\sqrt{\frac{2\log\beta}{T_i(t)}}$;
--   3. (24) $T_i(t)\le q_i\tau_i(1+\log t)+\sqrt{4q_i\tau_i(1+\log t)\log\beta+5\log^2\beta}$.
--
--   This collects Lemmas 4.5, 4.6 and 4.7 by a union bound. The deterministic analysis of §4.2 runs on this event.
--
--   **Formalization Note** The paper's display (23) omits the condition $T_i(t)\ge1$, which Lemma 4.6 carries. $\widehat H_{i,t}$ is undefined without it, so it is added here.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 17, §4.1, eq. (21), (23), (24)

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- §4.1, (21), (23), (24) (p. 17), stochastic model: with `β = 10Kn³δ⁻¹`, with probability at
least `1 - δ`, for every arm `i` and every time `t ∈ {1, …, τ₀}`:
(21) `|H̃_{i,t} - µ_i| ≤ √(4 (K min(τ_i,t)/t² + max(t-τ_i,0)/(q_i τ_i t)) log β
  + 5 (K log β/min(τ_i,t))²)`;
(23) if `T_i(t) ≥ 1`, `|Ĥ_{i,t} - µ_i| ≤ √(2 log β/T_i(t))`;
(24) `T_i(t) ≤ q_i τ_i (1 + log t) + √(4 q_i τ_i (1 + log t) log β + 5 log² β)`. -/
theorem union_event_stochastic (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) :
    1 - δ ≤ probStoch n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ν (fun ω I =>
      ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I),
        |estAvg (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) (tableAdv ω) I i t - mean ν i| ≤
            estRadius K (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i)
              (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i) t (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ∧
        (1 ≤ pullCount I i t →
          |algAvg (tableAdv ω) I i t - mean ν i| ≤
            Real.sqrt (2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) / pullCount I i t)) ∧
        (pullCount I i t : ℝ) ≤
            pullBound (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i)
              (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i) t (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ))) := by sorry

end BestBothWorlds.SAO
