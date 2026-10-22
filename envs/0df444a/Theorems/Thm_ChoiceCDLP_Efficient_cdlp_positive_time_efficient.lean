-- Prove2me | Theorems.Thm_ChoiceCDLP_Efficient_cdlp_positive_time_efficient
-- name    : ChoiceCDLP.Efficient.cdlp_positive_time_efficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T07:28:04.530908+00:00
-- url     : https://prove2.me/theorems/acea399a-b92a-42fd-8c59-f513857f9390
-- title:
--   Proposition 4 — every offer set with positive time in an optimal CDLP solution is efficient
-- statement:
--   In the network choice model, consider the choice-based deterministic linear program
--   $$\max \sum_{S \subseteq N} \lambda R(S)\, t(S) \quad\text{s.t.}\quad \sum_{S\subseteq N} \lambda Q(S)\, t(S) \le c,\qquad \sum_{S\subseteq N} t(S) \le \tau,\qquad t(S) \ge 0,$$
--   with arrival probability $0 < \lambda \le 1$, capacities $c \ge 0$ and horizon $\tau \ge 0$. If $t^*$ is an optimal solution and $t^*(T) > 0$ for an offer set $T$, then $T$ is efficient:
--   $$t^*(T) > 0 \ \Longrightarrow\ T \text{ is efficient.}$$
--
--   Efficiency is thus a defining property of the offer sets an optimal CDLP solution actually uses: inefficient sets can be discarded before solving the CDLP, for instance when generating columns.
--
--   **Formalization Note.** "$t^*(T) > 0$ is the optimal solution" is read as "$t^*$ is an optimal solution and $t^*(T) > 0$"; the CDLP may have several optimal solutions and the statement is made for every one of them, basic or not. The hypothesis $\lambda > 0$ is the paper's standing assumption that $\lambda$ is an arrival probability (its proof divides the reduced cost by $\lambda$); it is necessary: at $\lambda = 0$ the objective is identically zero, every feasible $t$ is optimal, and an inefficient set can receive positive time.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 296, Proposition 4

import Mathlib
import Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Efficient_IsEfficient
import Definitions.Def_ChoiceCDLP_Efficient_cdlpOptimal

namespace ChoiceCDLP.Efficient

/-- Proposition 4 (p. 296): if `t*` is an optimal solution of the CDLP (2) and `t*(T) > 0`,
then `T` is an efficient set. -/
theorem cdlp_positive_time_efficient {m n : ℕ} (N : ChoiceNetwork m n)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_le : lam ≤ 1)
    (c : Fin m → ℝ) (hc : 0 ≤ c) (τ : ℝ) (hτ : 0 ≤ τ)
    (t : Finset (Fin n) → ℝ) (ht : IsCDLPOptimal N lam c τ t)
    (T : Finset (Fin n)) (hT : 0 < t T) :
    IsEfficient N T := by sorry

end ChoiceCDLP.Efficient
