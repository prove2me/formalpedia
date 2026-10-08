-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_estimate_concentration_stochastic
-- name    : BestBothWorlds.SAO.estimate_concentration_stochastic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:45:47.875218+00:00
-- url     : https://prove2.me/theorems/6cbf72b9-6446-44de-8fb4-9d4c21832091
-- title:
--   Lemma 4.5 (stochastic model) — concentration of $\widetilde H_{i,t}$ around $\mu_i$
-- statement:
--   Consider SAO with parameter $\beta>1$ on $K\ge2$ arms and $n\ge K$ rounds in the stochastic model: distributions $\nu_1,\dots,\nu_K$ on $[0,1]$ with means $\mu_1,\dots,\mu_K$. Fix an arm $i$, a time $t\in\{1,\dots,n\}$ and $\delta>0$. With $\tau_0$, $\tau_i\leftarrow\min(\tau_i,\tau_0)$ and $q_i=p_{i,\min(\tau_i,\tau_0)}$ as in §4, with probability at least $1-\delta$, if $t\le\tau_0$ then
--   $$\big|\widetilde H_{i,t}-\mu_i\big|\le\sqrt{4\Big(\frac{K\min(\tau_i,t)}{t^2}+\frac{\max(t-\tau_i,0)}{q_i\tau_i t}\Big)\log(2t^2\delta^{-1})+5\Big(\frac{K\log(2t^2\delta^{-1})}{\min(\tau_i,t)}\Big)^2}.$$
--
--   The importance-weighted average $\widetilde H_{i,t}$ thus estimates $\mu_i$ at the rate of uniform exploration while arm $i$ is active, and at a degraded but controlled rate after it is deactivated. This is the source of (21).
--
--   **Formalization Note** The event is "$t\le\tau_0$ implies the bound" for one fixed pair $(i,t)$; the probability is not uniform in $t$.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 15, Lemma 4.5 (first display)

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- Lemma 4.5, stochastic part (p. 15): for a fixed arm `i` and time `t`, with probability at
least `1 - δ`, if `t ≤ τ₀` then
`|H̃_{i,t} - µ_i| ≤ √(4 (K min(τ_i,t)/t² + max(t-τ_i,0)/(q_i τ_i t)) log(2t²δ⁻¹)
  + 5 (K log(2t²δ⁻¹)/min(τ_i,t))²)`. -/
theorem estimate_concentration_stochastic (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (β : ℝ)
    (hβ : 1 < β) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (i : Fin K) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ probStoch n (sao K n β) ν (fun ω I =>
      t ≤ tau0 K n β (tableAdv ω) I →
        |estAvg (sao K n β) (tableAdv ω) I i t - mean ν i| ≤
          estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t
            (Real.log (2 * (t : ℝ) ^ 2 / δ))) := by sorry

end BestBothWorlds.SAO
