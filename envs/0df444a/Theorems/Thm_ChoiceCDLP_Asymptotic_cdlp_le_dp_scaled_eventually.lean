-- Prove2me | Theorems.Thm_ChoiceCDLP_Asymptotic_cdlp_le_dp_scaled_eventually
-- name    : ChoiceCDLP.Asymptotic.cdlp_le_dp_scaled_eventually
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:46:32.025344+00:00
-- url     : https://prove2.me/theorems/31409219-8df7-4057-b739-b0a7f87e7f34
-- title:
--   Proof of Proposition 2, constructed policy — liminf_{θ→∞} V*_θ/θ ≥ V^CDLP
-- statement:
--   For a choice-based network instance, capacities $c \in \mathbb{N}^m$ and horizon $T \in \mathbb{N}$, let $V^*_\theta = V^*(\theta c, \theta T)$ be the optimal expected revenue of the dynamic program (1) with capacities and horizon both scaled by $\theta \in \mathbb{N}$. Then for every $\varepsilon > 0$ there is $\Theta$ such that for all $\theta \ge \Theta$
--   $$V^{\mathrm{CDLP}}(c,T) - \varepsilon \le \frac{1}{\theta} V^*_\theta,$$
--   that is, $\liminf_{\theta\to\infty} \frac1\theta V^*_\theta \ge V^{\mathrm{CDLP}}$.
--
--   Together with Proposition 1 applied to the scaled instances and the scaling identity for the CDLP, this gives the first limit of Proposition 2.
--
--   **Formalization Note.** The paper proves this by constructing a policy that offers each set $S$ for $\theta t^*(S)$ periods and caps accepted demand at its mean; that policy uses fractional periods and rejects customers after they have chosen, neither of which is an action of the DP (1). The statement here is the paper's conclusion stated on the DP value itself, without the construction; it is true (standard fluid-limit argument), so this is not a repair. The $\liminf$ is written in its $\forall\varepsilon$, eventually form to avoid the junk value of `liminf` for sequences not known to be bounded. $\theta$ ranges over $\mathbb{N}$.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, pp. 294–295, proof of Proposition 2, second part (the constructed policy μ)

import Mathlib
import Definitions.Def_ChoiceCDLP_Asymptotic_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Asymptotic_cdlpValue
import Definitions.Def_ChoiceCDLP_Asymptotic_dpValue

namespace ChoiceCDLP.Asymptotic

/-- Proof of Proposition 2, second part (pp. 294–295): the scaled optimal expected revenue is
asymptotically at least `V^CDLP`, i.e. `liminf_{θ→∞} V*_θ / θ ≥ V^CDLP`, stated as: for every
`ε > 0`, eventually in `θ`, `V^CDLP - ε ≤ V*_θ / θ`. -/
theorem cdlp_le_dp_scaled_eventually {m n : ℕ} (N : ChoiceNetwork m n) (c : Fin m → ℕ) (T : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ θ : ℕ in Filter.atTop, cdlpValue N c T - ε ≤ dpValue N (θ • c) (θ * T) / (θ : ℝ) := by sorry

end ChoiceCDLP.Asymptotic
