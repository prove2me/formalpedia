-- Prove2me | Theorems.Thm_CurveSymmetry_family_projective_critical_eq_pair
-- name    : CurveSymmetry.family_projective_critical_eq_pair
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:37.310889+00:00
-- url     : https://prove2.me/theorems/2b3fac12-03e8-4af0-a4b3-0d8ea45ecaab
-- title:
--   The singular locus of $V_\alpha$ is exactly $\{(0,0),(\infty,\infty)\}$ for $m\ge2$ and $\alpha\notin\mathbb R$
-- statement:
--   Let $m\ge2$ be an integer and let $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$; no condition on $|\alpha|$ is imposed. For $x=(x_0,x_1)$ and $y=(y_0,y_1)$ in $\mathbb C^2$ let
--
--   $$
--   F_\alpha(x,y)=\alpha\,x_0^m x_1\,y_1^{m+1}+x_0^{m+1}y_0\,y_1^m+\bar\alpha\,x_1^{m+1}y_0^m\,y_1+x_0\,x_1^m\,y_0^{m+1},
--   $$
--
--   the bihomogenization of bidegree $(m+1,m+1)$ of $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$, and let $V_\alpha=\{F_\alpha=0\}\subset\mathbb P^1\times\mathbb P^1$. Let $\Sigma_\alpha$ be the set of its singular points by the Jacobian criterion: the points $([x],[y])$ such that $F_\alpha$, as a function on $\mathbb C^2\times\mathbb C^2$, vanishes at $(x,y)$ together with its differential. Identify the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$ with $\mathbb P^1$ by $\iota(z)=[z:1]$ for $z\in\mathbb C$ and $\iota(\infty)=[1:0]$.
--
--   Then
--
--   $$
--   \Sigma_\alpha=\bigl\{(\iota(0),\iota(0)),\ (\iota(\infty),\iota(\infty))\bigr\}=\bigl\{([0:1],[0:1]),\ ([1:0],[1:0])\bigr\}.
--   $$
--
--   This is the singular-point clause of Lemma 4 of the note: the only singular points of $V_\alpha$ are $(0,0)$ and $(\infty,\infty)$. It holds for every nonreal $\alpha$, without the condition $|\alpha|=1$; that both points are ordinary $m$-fold points is a separate statement. The proof of Theorem 2 relies on equivalences preserving this pair.
--
--   **Formalization Note**: $\iota$ is Mathlib's `OnePoint.equivProjectivization` from `OnePoint ℂ` to `Projectivization ℂ (Fin 2 → ℂ)`, and the singular locus is defined through `HasFDerivAt` at chosen representatives.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Lemma 4, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyGlobalSingularities.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
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
open OnePoint

theorem CurveSymmetry.family_projective_critical_eq_pair {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) :
    familyProjectiveCritical m α =
      {(sphereProjectiveEquiv ((0 : ℂ) : Sphere), sphereProjectiveEquiv ((0 : ℂ) : Sphere)),
        (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (∞ : Sphere))} := by sorry
