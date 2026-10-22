-- Prove2me | Theorems.Thm_ChoiceCDLP_Efficient_frontier_monotoneOn_concaveOn
-- name    : ChoiceCDLP.Efficient.frontier_monotoneOn_concaveOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T07:28:21.00012+00:00
-- url     : https://prove2.me/theorems/9deac511-e808-40c0-bbff-cdeaf243fb1e
-- title:
--   Appendix, proof of Proposition 3 — R̄(q) is increasing and concave on [0,1]^m
-- statement:
--   In the network choice model with revenues $R(S)$ and consumption vectors $Q(S)$, let
--   $$\bar R(q) = \max_{\alpha} \Big\{ \sum_S \alpha(S) R(S) : \sum_S \alpha(S) Q(S) \le q,\ \sum_S \alpha(S) = 1,\ \alpha \ge 0 \Big\}, \qquad q \in [0,1]^m .$$
--   Then $\bar R$ is increasing (for $q \le q'$ componentwise, $\bar R(q) \le \bar R(q')$) and concave on $[0,1]^m$.
--
--   This is the first step of the paper's proof of Proposition 3: the efficient sets are exactly the offer sets whose point $(Q(T), R(T))$ lies on the graph of the concave frontier $\bar R$, and a supporting hyperplane of $\bar R$ at $Q(T)$ gives the price vector $\pi$. The paper cites Theorem 5.1 of Bertsimas and Tsitsiklis (1997) for it (the optimal value of a linear program is concave in its right-hand side).
--
--   **Formalization Note.** "Increasing" is monotone non-decreasing in the componentwise order of $\mathbb{R}^m$. The domain is the paper's $[0,1]^m$ (`Set.Icc 0 1` in the Pi order); on it the defining set of $\bar R$ is nonempty and bounded above, so $\bar R$ is the paper's maximum.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 307, Appendix, proof of Proposition 3 (first display and the sentence after it)

import Mathlib
import Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Efficient_frontier

namespace ChoiceCDLP.Efficient

/-- Appendix, proof of Proposition 3 (p. 307): on `[0,1]^m` the frontier function `R̄` is
increasing and concave in `q`. -/
theorem frontier_monotoneOn_concaveOn {m n : ℕ} (N : ChoiceNetwork m n) :
    MonotoneOn (frontier N) (Set.Icc (0 : Fin m → ℝ) 1) ∧
      ConcaveOn ℝ (Set.Icc (0 : Fin m → ℝ) 1) (frontier N) := by sorry

end ChoiceCDLP.Efficient
