-- Prove2me | Theorems.Thm_ChoiceCDLP_Asymptotic_cdlpValue_scaled
-- name    : ChoiceCDLP.Asymptotic.cdlpValue_scaled
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:44:57.164849+00:00
-- url     : https://prove2.me/theorems/105eb8e0-782c-46c2-a11a-581d41e2315f
-- title:
--   Proof of Proposition 2, first paragraph — V^CDLP_θ = θ V^CDLP under scaling of capacity and horizon
-- statement:
--   For a choice-based network instance, capacities $c \in \mathbb{N}^m$, horizon $T \in \mathbb{N}$ and every scaling factor $\theta \in \mathbb{N}$, the CDLP with capacities $\theta c$ and horizon $\theta T$ has optimal value $\theta$ times that of the unscaled CDLP:
--   $$V^{\mathrm{CDLP}}_\theta := V^{\mathrm{CDLP}}(\theta c, \theta T) = \theta\, V^{\mathrm{CDLP}}(c, T).$$
--
--   This gives the second limit of Proposition 2 immediately: $\frac1\theta V^{\mathrm{CDLP}}_\theta = V^{\mathrm{CDLP}}$ for every $\theta \ge 1$.
--
--   **Formalization Note.** $\theta$ ranges over the natural numbers, since the scaled horizon $\theta T$ must be a whole number of periods; the case $\theta = 0$ is included (both sides are $0$). The paper phrases the claim as "$\theta t^*(S)$ is an optimal solution of the $\theta$-scaled CDLP with optimal value $\theta V^{\mathrm{CDLP}}$"; the statement here is the optimal-value identity, which does not depend on which optimal solution $t^*$ is chosen.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 294, proof of Proposition 2, first paragraph

import Mathlib
import Definitions.Def_ChoiceCDLP_Asymptotic_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Asymptotic_cdlpValue

namespace ChoiceCDLP.Asymptotic

/-- Proof of Proposition 2, first paragraph (p. 294): scaling capacity and horizon by `θ`
scales the CDLP optimal value by `θ`, `V^CDLP_θ = θ V^CDLP`. -/
theorem cdlpValue_scaled {m n : ℕ} (N : ChoiceNetwork m n) (c : Fin m → ℕ) (T θ : ℕ) :
    cdlpValue N (θ • c) (θ * T) = (θ : ℝ) * cdlpValue N c T := by sorry

end ChoiceCDLP.Asymptotic
