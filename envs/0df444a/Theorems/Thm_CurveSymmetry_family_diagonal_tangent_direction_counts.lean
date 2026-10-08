-- Prove2me | Theorems.Thm_CurveSymmetry_family_diagonal_tangent_direction_counts
-- name    : CurveSymmetry.family_diagonal_tangent_direction_counts
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:53.542444+00:00
-- url     : https://prove2.me/theorems/f24c1c39-ad69-4195-8a8d-5d4df71c2827
-- title:
--   The tangent cones $\alpha X^m+\bar\alpha Y^m$ and $u^m+v^m$ each vanish at exactly $m$ points of $\mathbb{P}^1$
-- statement:
--   Let $m\ge 1$ be an integer and let $\alpha\in\mathbb{C}$ with $\alpha\ne\bar\alpha$. For $a,b\in\mathbb{C}$ let $D_m(a,b)=\{[x:y]\in\mathbb{P}^1(\mathbb{C}) : ax^m+by^m=0\}$ be the set of points of the complex projective line at which the binary form $ax^m+by^m$ vanishes (a well-defined condition, since the form is homogeneous).
--
--   Then
--
--   $$\#D_m(\alpha,\bar\alpha)=m\qquad\text{and}\qquad\#D_m(1,1)=m:$$
--
--   each of the binary forms $\alpha x^m+\bar\alpha y^m$ and $x^m+y^m$ vanishes at exactly $m$ points of $\mathbb{P}^1(\mathbb{C})$.
--
--   In the proof of Lemma 4 of the note, $\alpha X^m+\bar\alpha Y^m$ and $u^m+v^m$, with $u=1/X$ and $v=1/Y$, are the tangent cones at $(0,0)$ and $(\infty,\infty)$ of $V_\alpha$, the closure in $\mathbb{P}^1\times\mathbb{P}^1$ of the curve $X^m(\alpha+XY)+Y^m(\bar\alpha+XY)=0$. The statement gives the $m$ distinct tangent directions at each of these two ordinary $m$-fold points.
--
--   **Formalization Note**: $\mathbb{P}^1(\mathbb{C})$ is the projectivization of $\mathbb{C}^2$; membership is tested on a chosen representative vector of each point, and the counts are `Nat.card`, so finiteness is included.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/BinaryTangentDirections.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
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

theorem CurveSymmetry.family_diagonal_tangent_direction_counts {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) :
    Nat.card (binaryTangentDirections m α (star α)) = m ∧
      Nat.card (binaryTangentDirections m 1 1) = m := by sorry
