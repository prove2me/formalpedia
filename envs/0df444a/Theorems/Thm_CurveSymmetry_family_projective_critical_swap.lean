-- Prove2me | Theorems.Thm_CurveSymmetry_family_projective_critical_swap
-- name    : CurveSymmetry.family_projective_critical_swap
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:40.755759+00:00
-- url     : https://prove2.me/theorems/34008f56-a50e-4dc5-8e03-94a27a9b8d46
-- title:
--   Swapping the factors of $\mathbb P^1\times\mathbb P^1$ exchanges the singular loci of $V_\alpha$ and $V_{\bar\alpha}$
-- statement:
--   Let $m\ge0$ be an integer and let $\alpha\in\mathbb C$ be arbitrary. For $\gamma\in\mathbb C$ and $x=(x_0,x_1)$, $y=(y_0,y_1)$ in $\mathbb C^2$ let
--
--   $$
--   F_\gamma(x,y)=\gamma\,x_0^m x_1\,y_1^{m+1}+x_0^{m+1}y_0\,y_1^m+\bar\gamma\,x_1^{m+1}y_0^m\,y_1+x_0\,x_1^m\,y_0^{m+1},
--   $$
--
--   the bihomogenization of $P_\gamma(X,Y)=X^m(\gamma+XY)+Y^m(\bar\gamma+XY)$, and let $V_\gamma=\{F_\gamma=0\}\subset\mathbb P^1\times\mathbb P^1$. Let $\Sigma_\gamma$ be the set of points $([x],[y])\in\mathbb P^1\times\mathbb P^1$ such that $F_\gamma$, viewed as a function on $\mathbb C^2\times\mathbb C^2$, vanishes at $(x,y)$ together with its differential (all four partial derivatives). This homogeneous Jacobian condition does not depend on the chosen representatives; it is the Jacobian criterion for the singular points of $V_\gamma$.
--
--   Then for every $(p_1,p_2)\in\mathbb P^1\times\mathbb P^1$
--
--   $$
--   (p_2,p_1)\in\Sigma_\alpha\iff(p_1,p_2)\in\Sigma_{\bar\alpha}.
--   $$
--
--   In the proof of Lemma 4 one mixed boundary point of $V_\alpha$ is treated from the other by exchanging $X$ and $Y$ and conjugating the coefficients; this is that symmetry at the level of singular points. The formalization uses it in the classification of the singular points of $V_\alpha$ and in the transport of singular points under anti-Möbius maps (Theorem 2).
--
--   **Formalization Note**: the condition is evaluated at chosen representatives in `Projectivization ℂ (Fin 2 → ℂ)`, with the vanishing differential expressed by `HasFDerivAt`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Theorem 2 (p. 2), Lemma 4 (p. 3), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/HomogeneousDifferential.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

open CurveSymmetry
set_option autoImplicit false

theorem CurveSymmetry.family_projective_critical_swap (m : ℕ) (α : ℂ)
    (p : ProjectiveLine × ProjectiveLine) :
    p.swap ∈ familyProjectiveCritical m α ↔ p ∈ familyProjectiveCritical m (star α) := by sorry
