-- Prove2me | Theorems.Thm_CurveSymmetry_criticalZero_homogeneousChart
-- name    : CurveSymmetry.criticalZero_homogeneousChart
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:49.571631+00:00
-- url     : https://prove2.me/theorems/82fe9b29-8683-467f-b093-5b99e0cdaa94
-- title:
--   Critical zeros of a bihomogeneous function and of its dehomogenization agree in the standard chart
-- statement:
--   Let $d\ge0$ be an integer and let $F:\mathbb C^2\times\mathbb C^2\to\mathbb C$ be any function that is bihomogeneous of bidegree $(d,d)$ in the sense that $F(ax,by)=a^d\,b^d\,F(x,y)$ for all $a,b\in\mathbb C$ and all $x,y\in\mathbb C^2$; no continuity is assumed. Let $\chi:\mathbb C^2\to\mathbb C^2\times\mathbb C^2$ be the standard chart $\chi(v_0,v_1)=\bigl((v_0,1),(v_1,1)\bigr)$ and let $f=F\circ\chi$, so that $f(v_0,v_1)=F\bigl((v_0,1),(v_1,1)\bigr)$ is the dehomogenization of $F$. Call $w$ a *critical zero* of a complex-valued function $H$ on $\mathbb C^2$ or on $\mathbb C^2\times\mathbb C^2$ if $H(w)=0$ and $H$ is complex differentiable at $w$ with zero differential.
--
--   Then for every $v\in\mathbb C^2$
--
--   $$
--   \chi(v)\ \text{is a critical zero of}\ F\iff v\ \text{is a critical zero of}\ f.
--   $$
--
--   This connects the homogeneous Jacobian condition on $\mathbb P^1\times\mathbb P^1$ with the Jacobian criterion for a dehomogenized equation. Combined with linear changes of coordinates, the formalization applies it in the four standard charts of $\mathbb P^1\times\mathbb P^1$, where the proof of Lemma 4 clears denominators and locates the singular points of $V_\alpha$.
--
--   **Formalization Note**: complex differentiability at $w$ with zero differential is `HasFDerivAt H 0 w` over $\mathbb C$; no differentiability of $F$ away from the point is assumed.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/HomogeneousCharts.lean (C. Perassi)

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
open Filter
open scoped Topology

theorem CurveSymmetry.criticalZero_homogeneousChart (F : HomogeneousPairs → ℂ) (d : ℕ)
    (hscale : ∀ (a b : ℂ) (q : HomogeneousPairs),
      F (a • q.1, b • q.2) = a ^ d * b ^ d * F q) (v : Fin 2 → ℂ) :
    CriticalZero F (homogeneousChart v) ↔ CriticalZero (F ∘ homogeneousChart) v := by sorry
