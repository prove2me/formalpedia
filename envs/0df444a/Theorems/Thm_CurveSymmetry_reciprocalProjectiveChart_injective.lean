-- Prove2me | Theorems.Thm_CurveSymmetry_reciprocalProjectiveChart_injective
-- name    : CurveSymmetry.reciprocalProjectiveChart_injective
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:05.691166+00:00
-- url     : https://prove2.me/theorems/ff84f74f-a6d8-48e1-8394-e5ecce9be911
-- title:
--   The chart $(u,v)\mapsto([1:u],[1:v])$ of $\mathbb P^1\times\mathbb P^1$ is injective
-- statement:
--   Let $\mathbb P^1$ be the complex projective line, the set of lines through the origin of $\mathbb C^2$, with homogeneous coordinates $[x_0:x_1]$. Under the usual identification of $[z:1]$ with $z\in\mathbb C$ and of $[1:0]$ with $\infty$, the point $[1:w]$ is $1/w$ (and $\infty$ when $w=0$). Consider the chart of $\mathbb P^1\times\mathbb P^1$ near $(X,Y)=(\infty,\infty)$, $\phi_3\colon\mathbb C^2\to\mathbb P^1\times\mathbb P^1$, $\phi_3(u,v)=([1:u],[1:v])$.
--
--   Then $\phi_3$ is injective: for all $u,v,u',v'\in\mathbb C$,
--
--   $$\bigl([1:u],[1:v]\bigr)=\bigl([1:u'],[1:v']\bigr)\ \Longrightarrow\ (u,v)=(u',v').$$
--
--   This is one of the four standard charts $\phi_0(X,Y)=([X:1],[Y:1])$, $\phi_1(u,Y)=([1:u],[Y:1])$, $\phi_2(v,X)=([X:1],[1:v])$ and $\phi_3(u,v)=([1:u],[1:v])$ of $\mathbb P^1\times\mathbb P^1$, in which $V_\alpha$, the closure of the curve (6) in $\mathbb P^1\times\mathbb P^1$, is described; the note introduces $V_\alpha$ before Lemma 4. Injectivity makes the chart a coordinate system on its image.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/ProjectiveChartMaps.lean (C. Perassi)

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
open OnePoint
set_option autoImplicit false

theorem CurveSymmetry.reciprocalProjectiveChart_injective : Function.Injective reciprocalProjectiveChart := by sorry
