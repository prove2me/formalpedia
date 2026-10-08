-- Prove2me | Theorems.Thm_CouplingHMC_Exact_eq_123
-- name    : CouplingHMC.Exact.eq_123
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:45.519353+00:00
-- url     : https://prove2.me/theorems/c1d7c712-8c17-46fb-bb83-f84afa3c436f
-- title:
--   (123), p. 38, at h = 0 — II ≤ (1/a) f′(r) P[W ≠ −γz] ≤ (γT/√(2π)) r f′(r) < (2/5) γT r f′(r)
-- statement:
--   Assume the hypotheses of Theorem 2.3: Assumption 2.1, the exact flow, $T>0$ with $LT^2\le\min(K/L,\tfrac14,\tfrac1{256L\mathcal R^2})$, and $\gamma,a,R_1,f$ as in (26)–(30). Let $x,y\in\mathbb R^d$ with $0<r=|x-y|<2\mathcal R$, so that $f'(r)=e^{-ar}$, and let $W=\xi-\eta$, $z=x-y$. Then
--
--   $$E\bigl[f(R'\wedge R_1)-f(r);\,W\ne-\gamma z\bigr]\le\frac1a f'(r)\,P[W\ne-\gamma z]\le\frac{\gamma T}{\sqrt{2\pi}}\,r f'(r)<\frac25\gamma T\,rf'(r).$$
--
--   This bounds the term II of the paper's decomposition: the loss in the distance on the event where the contractive coupling fails, after truncation at $R_1$.
--
--   **Formalization Note.** The signed integrand is included with its integrability, so Lean's Bochner integral represents the paper's expectation. The event probability is converted from $[0,\infty]$ to a real; it is finite because the noise law is a probability measure.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, §5, proof of Theorem 2.4, step (ii), term II, (123), pp. 37–38

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- (123), p. 38, at `h = 0`: under the hypotheses of Theorem 2.3 and `0 < r = |x - y| < 2ℛ`,
with `f'(r) = e^{-ar}`,
`II = E[f(R' ∧ R₁) - f(r); W ≠ -γz] ≤ (1/a) f'(r) P[W ≠ -γz] ≤ (γT/√(2π)) r f'(r) < (2/5) γT r f'(r)`.
The signed integrand is integrable, so the Bochner integral represents the paper's expectation. -/
theorem eq_123 {d : ℕ} (U : E d → ℝ) (L M N ℛ K : ℝ) (hU : Assumption21 U L M N ℛ K)
    (q p : ℝ → E d → E d → E d) (hflow : IsExactFlow U q p) (T : ℝ) (hT : 0 < T)
    (hTc : StepCond L K ℛ T) (x y : E d) (hr : 0 < ‖x - y‖) (hxy : ‖x - y‖ < 2 * ℛ) :
    IntegrableOn
      (fun ω : E d × ℝ =>
        fConc (aC T) (R1C T ℛ) (min (Rprime q T (gammaC T ℛ) ℛ x y ω) (R1C T ℛ)) -
          fConc (aC T) (R1C T ℛ) ‖x - y‖)
      {ω | couplingEta (gammaC T ℛ) ℛ x y ω.1 ω.2 ≠ ω.1 + gammaC T ℛ • (x - y)}
      (noiseLaw d) ∧
    (∫ ω in {ω : E d × ℝ | couplingEta (gammaC T ℛ) ℛ x y ω.1 ω.2 ≠ ω.1 + gammaC T ℛ • (x - y)},
        (fConc (aC T) (R1C T ℛ) (min (Rprime q T (gammaC T ℛ) ℛ x y ω) (R1C T ℛ)) -
          fConc (aC T) (R1C T ℛ) ‖x - y‖) ∂(noiseLaw d)) ≤
      1 / aC T * Real.exp (-(aC T * ‖x - y‖)) *
        (noiseLaw d {ω | couplingEta (gammaC T ℛ) ℛ x y ω.1 ω.2 ≠ ω.1 + gammaC T ℛ • (x - y)}).toReal ∧
    1 / aC T * Real.exp (-(aC T * ‖x - y‖)) *
        (noiseLaw d {ω | couplingEta (gammaC T ℛ) ℛ x y ω.1 ω.2 ≠ ω.1 + gammaC T ℛ • (x - y)}).toReal ≤
      gammaC T ℛ * T / Real.sqrt (2 * Real.pi) * ‖x - y‖ *
        Real.exp (-(aC T * ‖x - y‖)) ∧
    gammaC T ℛ * T / Real.sqrt (2 * Real.pi) * ‖x - y‖ * Real.exp (-(aC T * ‖x - y‖)) <
      2 / 5 * gammaC T ℛ * T * ‖x - y‖ * Real.exp (-(aC T * ‖x - y‖)) := by sorry

end CouplingHMC.Exact
