-- Prove2me | Theorems.Thm_AMPUniversality_Polytope_theorem_2
-- name    : AMPUniversality.Polytope.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:46.349528+00:00
-- url     : https://prove2.me/theorems/6fc218ef-c585-4b89-a0ce-e2afc4b6ed3b
-- title:
--   Theorem 2, p. 5 — universal weak neighborliness of projected cross-polytopes
-- statement:
--   Fix $\delta\in(0,1)$ and let $m(n)=\lfloor n\delta\rfloor$. For every sequence of random $m(n)\times n$ matrices $A(n)=\widetilde A(n)+\nu_0G(n)$, assume $\nu_0>0$, the entries of $A(n)$ are independent, centered, unit-variance, and sub-Gaussian with a common scale $s$ independent of $n$. The entries of $G(n)$ are independent standard normal variables, jointly independent of $\widetilde A(n)$. No independence between different values of $n$ is required.
--
--   Writing $C_n=\{x:\sum_i|x_i|\leq1\}$ and choosing the positive $\alpha$ with $f_\delta(\alpha)=\delta$, the projected polytopes $A(n)C_n$ have weak neighborliness $f_\rho(\alpha)$ in probability. Thus for every $\xi>0$,
--
--   $$\frac{F(A(n)C_n;m(n)f_\rho(\alpha)(1-\xi))}{F(C_n;m(n)f_\rho(\alpha)(1-\xi))}\to1,\qquad\frac{F(A(n)C_n;m(n)f_\rho(\alpha)(1+\xi))}{F(C_n;m(n)f_\rho(\alpha)(1+\xi))}\to0$$
--
--   in probability. Here $F(Q;\ell)$ counts the nonempty faces of dimension $\lfloor\ell\rfloor$. The result extends the Gaussian weak-neighborliness transition to every matrix law satisfying these hypotheses.
--
--   **Formalization Note** The parameter $\alpha$ is quantified with $f_\delta(\alpha)=\delta$ rather than obtained by a partial inverse; Footnote 3 states its unique existence. The cross-polytope uses the coordinate one-norm, and the matrix model uses the stated unit variance and an independent $N(0,1)$ component.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 5, Theorem 2

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_Neighborliness
import Definitions.Def_AMPUniversality_Polytope_Curve
import Definitions.Def_AMPUniversality_Polytope_Recovery

set_option autoImplicit false
open MeasureTheory
open scoped NNReal

namespace AMPUniversality.Polytope

/-- Theorem 2, p. 5: weak neighborliness of Gaussian-perturbed
sub-Gaussian projections of the cross-polytope. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Atil G : ∀ n, Ω → Matrix (Fin (rowCount δ n)) (Fin n) ℝ)
    (ν0 : ℝ) (hν : 0 < ν0) (s : ℝ≥0)
    (hG : HasGaussianComponent P (rowCount δ) Atil G (fun _ => 1))
    (hA : RectangularMatrixLaw P (rowCount δ)
      (perturbedMatrix (rowCount δ) Atil G ν0)
      (fun _ => 1) (fun _ => s))
    (α : ℝ) (hα : 0 < α) (hcurve : fδ α = δ) :
    HasWeakNeighborlinessInProb P (rowCount δ)
      (fun n ω => projPolytope
        (perturbedMatrix (rowCount δ) Atil G ν0 n ω)) (fρ α) := by sorry

end AMPUniversality.Polytope
