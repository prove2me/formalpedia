-- Prove2me | Theorems.Thm_FZEchelon_Discounted_lemma1_penalty_uniform
-- name    : FZEchelon.Discounted.lemma1_penalty_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:46:18.002234+00:00
-- url     : https://prove2.me/theorems/c9444f39-5fc9-42a1-9d6c-413f7ced9244
-- title:
--   Lemma 1, p. 826 — $\hat P_n - P$ is bounded ($n \ge 2$) and converges uniformly to $0$ on $\mathbb R$
-- statement:
--   In the two-echelon model of Federgruen and Zipkin under the standing assumptions of §1, assume $\alpha < 1$ and $\alpha^l p^r \ge (1-\alpha^l) h^d$. Let $x^{r*}$ be the critical number of the outlet problem and $x_n^{r*}$ ($n \ge 1$) those of program (2). Let $\hat P_n$ be the finite-horizon induced penalty costs and $P$ the stationary one. Then:
--
--   1. for every $n \ge 2$, the difference $\hat P_n - P$ is bounded on $\mathbb R$;
--   2. $\hat P_n \to P$ uniformly on the entire real line:
--   $$
--   \sup_{x \in \mathbb R} |\hat P_n(x) - P(x)| \to 0 \qquad (n \to \infty).
--   $$
--
--   Lemma 1 says that the nonstationary penalties of the finite-horizon depot program (3) approach the stationary penalty of the depot problem $IH_\alpha^d$. It is the first step in replacing $\hat g_n^d$ by $g_n^d$.
--
--   **Formalization Note.** The paper says the differences are bounded with no restriction on $n$. For $n = 1$ this fails when $\alpha > 0$: $g_0^r = 0$, so $\hat P_1(x) - P(x) = \alpha c^r x + \text{const}$ for $x$ below $\min(x_1^{r*}, x^{r*})$. The paper's proof bounds $\gamma_n$ by $2\alpha\beta_{n-1}$ plus finite terms, which is finite exactly for $n \ge 2$. Boundedness is therefore stated for $n \ge 2$; uniform convergence, a statement about large $n$, is as printed.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 826, Lemma 1

import Mathlib
import Definitions.Def_FZEchelon_Discounted_Programs

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

/-- Lemma 1, p. 826: the differences `P̂_n − P` are bounded (for every `n ≥ 2`) and converge
uniformly to the zero function on the entire real line. -/
theorem lemma1_penalty_uniform (M : Model) (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (xn : ℕ → ℝ) (hxn : M.IsCriticalNumberSeq xn) :
    (∀ n, 2 ≤ n → ∃ C : ℝ, ∀ x, |M.Phat xn n x - M.P xstar x| ≤ C) ∧
      TendstoUniformly (M.Phat xn) (M.P xstar) atTop := by sorry

end FZEchelon.Discounted
