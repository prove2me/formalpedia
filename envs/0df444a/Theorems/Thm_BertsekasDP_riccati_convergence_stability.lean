-- Prove2me | Theorems.Thm_BertsekasDP_riccati_convergence_stability
-- name    : BertsekasDP.riccati_convergence_stability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:37:17.275878+00:00
-- url     : https://prove2.me/theorems/69c7bbc7-59ef-4272-bc49-bf202fd0e074
-- title:
--   Riccati convergence and closed-loop stability (Prop. 4.4.1)
-- statement:
--   **Proposition 4.4.1 (asymptotic behavior of the Riccati equation and closed-loop stability).** Let $A$ be $n \times n$, $B$ be $n \times m$, let $Q$ be positive semidefinite symmetric with $Q = C^{\top} C$, and let $R$ be positive definite symmetric. Assume that $(A,B)$ is **controllable** and that $(A,C)$ is **observable**. Then there is a positive definite symmetric matrix $P$ such that:
--
--   1. **$P$ solves the algebraic Riccati equation:**
--   $$P \;=\; A^{\top}\Bigl(P - P B \bigl(B^{\top} P B + R\bigr)^{-1} B^{\top} P\Bigr) A + Q ;$$
--   2. **$P$ is the only positive semidefinite solution:** every positive semidefinite fixed point of the Riccati operator equals $P$;
--   3. **the Riccati iteration converges to $P$ from every positive semidefinite start:**
--   $$\lim_{k \to \infty} P_k \;=\; P \qquad \text{whenever } P_{k+1} = F(P_k), \; P_0 \succeq 0 ;$$
--   4. **the closed loop is stable:** with the stationary gain $L = -\bigl(B^{\top} P B + R\bigr)^{-1} B^{\top} P A$, every eigenvalue $\lambda$ of $A + BL$ satisfies
--   $$|\lambda| \;<\; 1 .$$
--
--   This is the mathematical warrant for steady-state LQR design: it says the design equation has exactly one meaningful solution, that iterating the finite-horizon recursion finds it, and that the resulting constant feedback law stabilizes the system. Without part 4 one could compute a gain that minimizes cost over a finite horizon yet drives the state to infinity as the horizon grows.
--
--   **Formalization Note** Positive semidefiniteness and definiteness are Mathlib's (symmetry included). Uniqueness is asserted within the positive semidefinite cone only; nothing is claimed about indefinite fixed points. Convergence is entrywise, equivalently in any matrix norm. Eigenvalues are taken as the spectrum of the complexified matrix, so the bound is on the complex modulus. Matrix inverses are Mathlib's total inverse; part of the proof burden is showing $B^{\top}PB + R$ is invertible where it is used.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 4.4.1 (Section 4.1)

import Mathlib
import Definitions.Def_BertsekasRiccatiMap

open Matrix

namespace BertsekasDP

theorem riccati_convergence_stability {n m q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin q) (Fin n) ℝ)
    (hQ : Q = Cᵀ * C) (hQpsd : Q.PosSemidef) (hR : R.PosDef)
    (hctrb : BertsekasControllablePair A B)
    (hobs : BertsekasObservablePair A C) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, P.PosDef ∧
      BertsekasRiccatiMap A B Q R P = P ∧
      (∀ P' : Matrix (Fin n) (Fin n) ℝ, P'.PosSemidef →
        BertsekasRiccatiMap A B Q R P' = P' → P' = P) ∧
      (∀ P₀ : Matrix (Fin n) (Fin n) ℝ, P₀.PosSemidef →
        Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] P₀)
          Filter.atTop (nhds P)) ∧
      (∀ z ∈ spectrum ℂ
          ((A + B * (-((Bᵀ * P * B + R)⁻¹ * Bᵀ * P * A))).map
            (algebraMap ℝ ℂ)),
        ‖z‖ < 1) := by sorry

end BertsekasDP
