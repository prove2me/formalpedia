-- Prove2me | Theorems.Thm_CurveSymmetry_sphericalFamily_projective_iff
-- name    : CurveSymmetry.sphericalFamily_projective_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:09.76914+00:00
-- url     : https://prove2.me/theorems/9abdad65-cf06-446a-b247-b7a5b8318f9a
-- title:
--   The sphere, embedded by $p\mapsto(p,\bar p)$, meets $V_\alpha$ exactly in the spherical closure $\widehat C_{m,\alpha}$
-- statement:
--   Let $m\ge 1$ be an integer and let $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$, that is, $\alpha\notin\mathbb R$; no condition on $|\alpha|$ is imposed. Let $C_{m,\alpha}=\{z\in\mathbb C:\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$ and let $\widehat C_{m,\alpha}$ be its closure in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$. Complex conjugation $p\mapsto\bar p$ acts on $\widehat{\mathbb C}$, with $\bar\infty=\infty$.
--
--   Identify $\widehat{\mathbb C}$ with the complex projective line $\mathbb P^1$ by $\iota(z)=[z:1]$ for $z\in\mathbb C$ and $\iota(\infty)=[1:0]$. For $x=(x_0,x_1)$ and $y=(y_0,y_1)$ in $\mathbb C^2$ let
--
--   $$
--   F_\alpha(x,y)=\alpha\,x_0^m x_1\,y_1^{m+1}+x_0^{m+1}y_0\,y_1^m+\bar\alpha\,x_1^{m+1}y_0^m\,y_1+x_0\,x_1^m\,y_0^{m+1},
--   $$
--
--   the bihomogeneous form of bidegree $(m+1,m+1)$ with $F_\alpha\bigl((X,1),(Y,1)\bigr)=P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$, and let $V_\alpha=\{([x],[y])\in\mathbb P^1\times\mathbb P^1:F_\alpha(x,y)=0\}$ be its zero set.
--
--   Then for every $p\in\widehat{\mathbb C}$
--
--   $$
--   \bigl(\iota(p),\,\iota(\bar p)\bigr)\in V_\alpha\iff p\in\widehat C_{m,\alpha}.
--   $$
--
--   The note complexifies the plane curve by $X=z$, $Y=\bar z$ and considers the closure $V_\alpha$ of the curve $P_\alpha=0$ of equation (6) in $\mathbb P^1\times\mathbb P^1$, which is given by the bihomogeneous equation above. This result says that the sphere, embedded in $\mathbb P^1\times\mathbb P^1$ by $p\mapsto(p,\bar p)$, meets $V_\alpha$ exactly in $\widehat C_{m,\alpha}$, the point at infinity included. The formalization uses it to pass between Möbius maps of the sphere and the induced maps of $\mathbb P^1\times\mathbb P^1$, as in the proof of Theorem 2.
--
--   **Formalization Note**: the sphere is `OnePoint ℂ`, $\mathbb P^1$ is `Projectivization ℂ (Fin 2 → ℂ)` and $\iota$ is Mathlib's `OnePoint.equivProjectivization`. $V_\alpha$ is defined as the zero set of $F_\alpha$ evaluated on chosen representatives, which is harmless because $F_\alpha$ is bihomogeneous, and $\widehat C_{m,\alpha}$ is the topological closure in `OnePoint ℂ`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3; proof of Lemma 4, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyProjective.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

open CurveSymmetry
set_option autoImplicit false
open OnePoint

theorem CurveSymmetry.sphericalFamily_projective_iff {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (p : Sphere) :
    sphereRealDiagonal p ∈ familyProjectiveCurve m α ↔ p ∈ sphericalFamily m α := by sorry
