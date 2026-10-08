-- Prove2me | Theorems.Thm_CouplingHMC_Exact_term_III_tail
-- name    : CouplingHMC.Exact.term_III_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:37.31698+00:00
-- url     : https://prove2.me/theorems/ee92067f-d62a-49b0-9a09-c51fb17aed98
-- title:
--   §5, proof of Theorem 2.4, step (ii), term III, p. 39 — E[(R′ − R₁)⁺; W ≠ −γz] ≤ (5/4)γrT
-- statement:
--   Assume the hypotheses of Theorem 2.3, with $\gamma$ and $R_1$ as in (28) and (30). Let $x,y\in\mathbb R^d$ with $0<r=|x-y|<2\mathcal R$, $z=x-y$ and $W=\xi-\eta$. Then
--
--   $$E\bigl[(R'-R_1)^+;\,W\ne-\gamma z\bigr]\le\frac54\,\gamma rT.$$
--
--   On the event where the reflection branch of the coupling is used, the distance after one step exceeds $R_1$ only by an amount whose expectation is of order $\gamma rT$. This controls the term III of the decomposition.
--
--   **Formalization Note.** At $h=0$ the acceptance events are the whole space. The positive part $(\cdot)^+$ is taken inside the integral, as on the page.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, §5, proof of Theorem 2.4, step (ii), term III, p. 39

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- §5, proof of Theorem 2.4, step (ii), term III (p. 39), at `h = 0`: under the hypotheses of
Theorem 2.3 and `0 < r = |x - y| < 2ℛ`, `E[(R' - R₁)⁺; W ≠ -γz] ≤ (5/4) γ r T`. -/
theorem term_III_tail {d : ℕ} (U : E d → ℝ) (L M N ℛ K : ℝ) (hU : Assumption21 U L M N ℛ K)
    (q p : ℝ → E d → E d → E d) (hflow : IsExactFlow U q p) (T : ℝ) (hT : 0 < T)
    (hTc : StepCond L K ℛ T) (x y : E d) (hr : 0 < ‖x - y‖) (hxy : ‖x - y‖ < 2 * ℛ) :
    ∫⁻ ω in {ω : E d × ℝ | couplingEta (gammaC T ℛ) ℛ x y ω.1 ω.2 ≠ ω.1 + gammaC T ℛ • (x - y)},
        ENNReal.ofReal (Rprime q T (gammaC T ℛ) ℛ x y ω - R1C T ℛ) ∂(noiseLaw d) ≤
      ENNReal.ofReal (5 / 4 * gammaC T ℛ * ‖x - y‖ * T) := by sorry

end CouplingHMC.Exact
