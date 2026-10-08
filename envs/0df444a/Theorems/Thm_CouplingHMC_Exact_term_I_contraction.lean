-- Prove2me | Theorems.Thm_CouplingHMC_Exact_term_I_contraction
-- name    : CouplingHMC.Exact.term_I_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:47.152618+00:00
-- url     : https://prove2.me/theorems/595a45a9-fd67-464f-8877-25e7b8332901
-- title:
--   §5, proof of Theorem 2.4, step (ii), term I, p. 37 — on {W = −γz}, R′ ≤ (1 − ¾γT) r
-- statement:
--   Suppose Assumption 2.1 holds, $(q_t,p_t)$ is the exact Hamiltonian flow, $T>0$ satisfies $LT^2\le\min(K/L,\tfrac14,\tfrac1{256L\mathcal R^2})$, and $\gamma=\min(T^{-1},\mathcal R^{-1}/4)$. Let $x,y\in\mathbb R^d$ with $|x-y|<2\mathcal R$ and $z=x-y$. On the event $W=\xi-\eta=-\gamma z$ of the coupling, that is $\eta=\xi+\gamma z$, for every $\xi\in\mathbb R^d$,
--
--   $$R'=|q_T(x,\xi)-q_T(y,\xi+\gamma z)|\le\Bigl(1-\frac34\gamma T\Bigr)|x-y|.$$
--
--   This is the contractive part of the coupling for nearby points: the velocity shift $\gamma z$ steers the two trajectories towards each other.
--
--   **Formalization Note.** At $h=0$ both acceptance events are the whole space, so $A(x)\cap\hat A(y)\cap\{W=-\gamma z\}=\{W=-\gamma z\}$.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, §5, proof of Theorem 2.4, step (ii), term I, with (121), p. 37

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- §5, proof of Theorem 2.4, step (ii), term I (p. 37), at `h = 0`: under the hypotheses of
Theorem 2.3 and `|x - y| < 2ℛ`, on the event `W = ξ - η = -γz` (i.e. `η = ξ + γz`, `z = x - y`),
`R' = |q_T(x, ξ) - q_T(y, ξ + γz)| ≤ (1 - ¾γT) r`, for every `ξ`. -/
theorem term_I_contraction {d : ℕ} (U : E d → ℝ) (L M N ℛ K : ℝ) (hU : Assumption21 U L M N ℛ K)
    (q p : ℝ → E d → E d → E d) (hflow : IsExactFlow U q p) (T : ℝ) (hT : 0 < T)
    (hTc : StepCond L K ℛ T) (x y : E d) (hxy : ‖x - y‖ < 2 * ℛ) (ξ : E d) :
    ‖q T x ξ - q T y (ξ + gammaC T ℛ • (x - y))‖ ≤
      (1 - 3 / 4 * gammaC T ℛ * T) * ‖x - y‖ := by sorry

end CouplingHMC.Exact
