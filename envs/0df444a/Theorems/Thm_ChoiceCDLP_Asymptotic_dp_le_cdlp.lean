-- Prove2me | Theorems.Thm_ChoiceCDLP_Asymptotic_dp_le_cdlp
-- name    : ChoiceCDLP.Asymptotic.dp_le_cdlp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:46:09.88147+00:00
-- url     : https://prove2.me/theorems/97083e6d-6b03-4087-bc02-43fa0b4595b3
-- title:
--   Proposition 1 — V* ≤ V^CDLP: the CDLP value bounds the optimal expected revenue
-- statement:
--   Let a choice-based network instance be given (0/1 incidence matrix $A$, revenues $r$, arrival probability $\lambda \in [0,1]$, choice probabilities $P_j(S)$ with $P_j(S)\ge 0$, $P_j(S) = 0$ for $j\notin S$, $\sum_{j \in S} P_j(S) \le 1$). For every capacity vector $c \in \mathbb{N}^m$ and every horizon $T \in \mathbb{N}$, the optimal expected revenue of the dynamic program (1) is at most the optimal value of the CDLP (2):
--   $$V^*(c,T) \le V^{\mathrm{CDLP}}(c,T).$$
--
--   The CDLP is therefore an upper bound for every instance, and in particular for every $\theta$-scaled instance $(\theta c, \theta T)$; this is the upper half of the asymptotic optimality result.
--
--   **Formalization Note.** $V^*$ is the DP value $V_1(c)$ of (1) with the no-overbooking restriction (see `dpValue`); $V^{\mathrm{CDLP}}$ is the optimal value of (2) (see `cdlpValue`).
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 294, Proposition 1

import Mathlib
import Definitions.Def_ChoiceCDLP_Asymptotic_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Asymptotic_cdlpValue
import Definitions.Def_ChoiceCDLP_Asymptotic_dpValue

namespace ChoiceCDLP.Asymptotic

/-- Proposition 1 (p. 294): the CDLP value is an upper bound on the optimal expected revenue,
`V* ≤ V^CDLP`, for every initial capacity `c` and horizon `T`. -/
theorem dp_le_cdlp {m n : ℕ} (N : ChoiceNetwork m n) (c : Fin m → ℕ) (T : ℕ) :
    dpValue N c T ≤ cdlpValue N c T := by sorry

end ChoiceCDLP.Asymptotic
