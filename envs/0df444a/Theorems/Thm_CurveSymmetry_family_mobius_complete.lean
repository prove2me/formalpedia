-- Prove2me | Theorems.Thm_CurveSymmetry_family_mobius_complete
-- name    : CurveSymmetry.family_mobius_complete
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:59.775753+00:00
-- url     : https://prove2.me/theorems/82d541f3-edba-4497-ac4e-1fae73db150a
-- title:
--   A Möbius map sending $\widehat C_{m,\alpha}$ into $\widehat C_{m,\beta}$ is $z\mapsto cz$ or $z\mapsto c/z$ with $c\ne0$
-- statement:
--   Let $m\ge2$ be an integer and let $\alpha,\beta\in\mathbb C$ with $\alpha\ne\bar\alpha$ and $\beta\ne\bar\beta$; no condition on their moduli is imposed. For $\gamma\in\{\alpha,\beta\}$ let $\widehat C_{m,\gamma}$ be the closure in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$ of $C_{m,\gamma}=\{z\in\mathbb C:\operatorname{Re}\bigl(z^m(|z|^2+\gamma)\bigr)=0\}$. Let $g=(g_{ij})\in\mathrm{GL}_2(\mathbb C)$ be any invertible matrix and $M_g(z)=\frac{g_{11}z+g_{12}}{g_{21}z+g_{22}}$ the Möbius transformation of $\widehat{\mathbb C}$ it defines, with the usual conventions at the pole and at $\infty$. For $c\in\mathbb C$ let $\delta_c,s_c:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be given by $\delta_c(z)=cz$ for $z\in\mathbb C$, $\delta_c(\infty)=\infty$, and by $s_c(z)=c/z$ for $z\in\mathbb C\setminus\{0\}$, $s_c(0)=\infty$, $s_c(\infty)=0$.
--
--   Assume that $M_g(\widehat C_{m,\alpha})\subseteq\widehat C_{m,\beta}$. Then there is $c\in\mathbb C$ with $c\ne0$ such that
--
--   $$
--   M_g(p)=\delta_c(p)\ \text{ for all } p\in\widehat{\mathbb C}\qquad\text{or}\qquad M_g(p)=s_c(p)\ \text{ for all } p\in\widehat{\mathbb C}.
--   $$
--
--   In the proof of Theorem 2 every equivalence is reduced to one of the forms $cz$, $c/z$, $c\bar z$, $c/\bar z$; this is the holomorphic case. Only an inclusion is assumed, the matrix is arbitrary, and no preservation of the pair $\{0,\infty\}$ is assumed. The coefficient comparison (8) then leads to the symmetry group (3) of Theorem 2.
--
--   **Formalization Note**: the sphere is `OnePoint ℂ` with Mathlib's action of `GL (Fin 2) ℂ`, and both forms are asserted at every point of `OnePoint ℂ`, including $0$ and $\infty$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Theorem 2, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyGlobalSingularities.lean (C. Perassi)

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

theorem CurveSymmetry.family_mobius_complete {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β) :
    ∃ c : ℂ, c ≠ 0 ∧ ((∀ p : Sphere, g • p = sphereDilation c p) ∨
      (∀ p : Sphere, g • p = sphereInversion c p)) := by sorry
