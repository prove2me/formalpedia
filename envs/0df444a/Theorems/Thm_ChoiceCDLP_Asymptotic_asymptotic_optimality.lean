-- Prove2me | Theorems.Thm_ChoiceCDLP_Asymptotic_asymptotic_optimality
-- name    : ChoiceCDLP.Asymptotic.asymptotic_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:46:40.528184+00:00
-- url     : https://prove2.me/theorems/53443e20-d21a-48df-9b75-a65f2c49692e
-- title:
--   Proposition 2 — lim (1/θ)V*_θ = lim (1/θ)V^CDLP_θ = V^CDLP: the CDLP is asymptotically optimal
-- statement:
--   Consider a choice-based network revenue management instance: $m$ legs, $n$ products, a 0/1 incidence matrix $A$, revenues $r_j$, a per-period arrival probability $\lambda \in [0,1]$, and time-homogeneous choice probabilities $P_j(S)$ with $P_j(S) \ge 0$, $P_j(S) = 0$ for $j \notin S$ and $\sum_{j\in S}P_j(S) \le 1$. Fix capacities $c \in \mathbb{N}^m$ and a horizon $T \in \mathbb{N}$. For $\theta \in \mathbb{N}$, the **$\theta$-scaled problems** have capacities $\theta c$ and $\theta T$ periods; let $V^*_\theta$ be the optimal expected revenue of the dynamic program (1) for the scaled problem and $V^{\mathrm{CDLP}}_\theta$ the optimal value of the scaled CDLP (2). Then
--   $$\lim_{\theta\to\infty} \frac{1}{\theta} V^*_\theta \;=\; \lim_{\theta\to\infty} \frac{1}{\theta} V^{\mathrm{CDLP}}_\theta \;=\; V^{\mathrm{CDLP}},$$
--   where $V^{\mathrm{CDLP}}$ is the optimal value of the unscaled CDLP.
--
--   The CDLP is thus asymptotically tight: its value, which upper-bounds the optimal expected revenue for every instance, is matched to first order by the optimal revenue when capacity and demand grow proportionally.
--
--   **Formalization Note.** Both limits are stated as `Tendsto` along `θ : ℕ` to `atTop`, with $\frac1\theta$ as real division. $\theta$ is a natural number because the scaled horizon $\theta T$ must be a whole number of periods; the paper does not specify the range of $\theta$. $V^*_\theta$ is the DP value (1) with the no-overbooking restriction; both capacity and horizon are scaled.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 294, Proposition 2

import Mathlib
import Definitions.Def_ChoiceCDLP_Asymptotic_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Asymptotic_cdlpValue
import Definitions.Def_ChoiceCDLP_Asymptotic_dpValue

open Filter Topology

namespace ChoiceCDLP.Asymptotic

/-- Proposition 2 (p. 294): under proportional scaling of capacity (`θ c`) and horizon
(`θ T`), `lim_{θ→∞} V*_θ / θ = lim_{θ→∞} V^CDLP_θ / θ = V^CDLP`. -/
theorem asymptotic_optimality {m n : ℕ} (N : ChoiceNetwork m n) (c : Fin m → ℕ) (T : ℕ) :
    Tendsto (fun θ : ℕ => dpValue N (θ • c) (θ * T) / (θ : ℝ)) atTop (𝓝 (cdlpValue N c T)) ∧
    Tendsto (fun θ : ℕ => cdlpValue N (θ • c) (θ * T) / (θ : ℝ)) atTop
      (𝓝 (cdlpValue N c T)) := by sorry

end ChoiceCDLP.Asymptotic
