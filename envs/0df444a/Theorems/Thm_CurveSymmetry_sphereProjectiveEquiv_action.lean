-- Prove2me | Theorems.Thm_CurveSymmetry_sphereProjectiveEquiv_action
-- name    : CurveSymmetry.sphereProjectiveEquiv_action
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:10.949704+00:00
-- url     : https://prove2.me/theorems/c715aabf-5708-42a9-9f61-9df3b88f7f33
-- title:
--   The identification of the Riemann sphere with $\mathbb P^1(\mathbb C)$ is $\mathrm{GL}_2(\mathbb C)$-equivariant
-- statement:
--   Let $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$ be the Riemann sphere, let $\mathbb P^1(\mathbb C)$ be the projective line of one-dimensional subspaces of $\mathbb C^2$, and let $\Phi:\widehat{\mathbb C}\to\mathbb P^1(\mathbb C)$ be the standard bijection, $\Phi(z)=[z:1]$ for $z\in\mathbb C$ and $\Phi(\infty)=[1:0]$. An invertible matrix $g\in\mathrm{GL}_2(\mathbb C)$ with rows $(a,b)$ and $(c,d)$ acts on $\mathbb P^1(\mathbb C)$ by $g\cdot[v]=[gv]$, and on $\widehat{\mathbb C}$ as a Möbius transformation: $g\cdot z=\frac{az+b}{cz+d}$ if $cz+d\ne0$ and $g\cdot z=\infty$ if $cz+d=0$, while $g\cdot\infty=a/c$ if $c\ne0$ and $g\cdot\infty=\infty$ if $c=0$.
--
--   Then for every $g\in\mathrm{GL}_2(\mathbb C)$ and every $p\in\widehat{\mathbb C}$,
--   $$\Phi(g\cdot p)=g\cdot\Phi(p).$$
--
--   This lets the ambient Möbius maps of Theorem 2, which act on the Riemann sphere containing $\widehat C_{m,\alpha}$, be treated as projective linear maps of $\mathbb P^1$, the factor of the surface $\mathbb P^1\times\mathbb P^1$ in which the compactification $V_\alpha$ of Lemma 4 lies. Every invertible matrix is allowed, not only the forms singled out in Theorem 2.
--
--   **Formalization Note**: the Riemann sphere is Mathlib's one-point compactification `OnePoint ℂ`, $\mathbb P^1(\mathbb C)$ is the projectivization of $\mathbb C^2$, and $\Phi$ is Mathlib's standard bijection between them, used as a bijection of sets (no topological statement is made); both actions are Mathlib's actions of $\mathrm{GL}_2(\mathbb C)$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Theorem 2 (p. 2), Lemma 4 (p. 3), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/SphereGeometry.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
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
open scoped LinearAlgebra.Projectivization
open OnePoint

theorem CurveSymmetry.sphereProjectiveEquiv_action (g : MobiusMatrix) (p : Sphere) :
    sphereProjectiveEquiv (g • p) = g • sphereProjectiveEquiv p := by sorry
