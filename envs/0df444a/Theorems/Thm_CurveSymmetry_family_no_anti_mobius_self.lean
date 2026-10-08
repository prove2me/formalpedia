-- Prove2me | Theorems.Thm_CurveSymmetry_family_no_anti_mobius_self
-- name    : CurveSymmetry.family_no_anti_mobius_self
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:36.016412+00:00
-- url     : https://prove2.me/theorems/765916bd-c1a2-4dc9-acaf-6ff9ddcb0118
-- title:
--   No anti-Möbius map carries $\widehat C_{m,\alpha}$ into itself
-- statement:
--   Let $m\ge2$ be an integer and let $\alpha\in\mathbb C$ with $|\alpha|=1$ and $\alpha\notin\mathbb R$. Let $C_{m,\alpha}=\{z\in\mathbb C:\operatorname{Re}(z^m(|z|^2+\alpha))=0\}$ and let $\widehat C_{m,\alpha}$ be its closure in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$. A matrix $g=(g_{jk})\in\mathrm{GL}_2(\mathbb C)$ acts on $\widehat{\mathbb C}$ by the Möbius transformation $g\cdot z=\dfrac{g_{11}z+g_{12}}{g_{21}z+g_{22}}$, with the usual conventions at the pole and at $\infty$. Let $\kappa\colon\widehat{\mathbb C}\to\widehat{\mathbb C}$ be complex conjugation, $\kappa(z)=\bar z$, $\kappa(\infty)=\infty$, so that $g\circ\kappa\colon p\mapsto g\cdot\kappa(p)$ is an anti-Möbius map.
--
--   Then for every $g\in\mathrm{GL}_2(\mathbb C)$ the anti-Möbius map $g\circ\kappa$ does not carry $\widehat C_{m,\alpha}$ into itself:
--
--   $$(g\circ\kappa)(\widehat C_{m,\alpha})\nsubseteq\widehat C_{m,\alpha}.$$
--
--   This is the assertion of Theorem 2 that $\widehat C_{m,\alpha}$ has no anti-Möbius symmetry, in one-sided form: no anti-Möbius map even carries the curve into itself. In the formalization it is also used to exclude self-maps of $C_{m,\alpha}$ of the form $z\mapsto a\bar z+b$ with $a\ne0$; it supports Theorems 1 and 2.
--
--   **Formalization Note**: the Riemann sphere is the one-point compactification `OnePoint ℂ` and the curves are topological closures in it; matrices act through Mathlib's identification of the sphere with the projective line, and conjugation acts on the sphere fixing $\infty$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Theorem 2, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilySphereClassification.lean (C. Perassi)

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

theorem CurveSymmetry.family_no_anti_mobius_self {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (g : MobiusMatrix) :
    ¬ (∀ p ∈ sphericalFamily m α,
      g • OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m α) := by sorry
