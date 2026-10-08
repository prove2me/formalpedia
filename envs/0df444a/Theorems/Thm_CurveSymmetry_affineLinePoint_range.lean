-- Prove2me | Theorems.Thm_CurveSymmetry_affineLinePoint_range
-- name    : CurveSymmetry.affineLinePoint_range
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:36.706536+00:00
-- url     : https://prove2.me/theorems/d0459e86-6301-4103-bbe6-e98ac0059863
-- title:
--   The chart $z\mapsto[z:1]$ of $\mathbb P^1$ misses exactly the point at infinity
-- statement:
--   Let $\mathbb P^1$ be the complex projective line, the set of lines through the origin of $\mathbb C^2$, with homogeneous coordinates $[x_0:x_1]$. Let $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$ be the Riemann sphere and let $\iota\colon\widehat{\mathbb C}\to\mathbb P^1$ be the standard bijection, $\iota(z)=[z:1]$ for $z\in\mathbb C$ and $\iota(\infty)=[1:0]$.
--
--   Then for every $p\in\mathbb P^1$,
--
--   $$p\in\bigl\{[z:1]\ :\ z\in\mathbb C\bigr\}\iff p\ne\iota(\infty)=[1:0].$$
--
--   That is, the finite chart $z\mapsto[z:1]$ omits exactly the point at infinity.
--
--   Together with its companion for the other chart of $\mathbb P^1$, it is used to describe the overlaps of the four standard charts of $\mathbb P^1\times\mathbb P^1$ and to show that their images are open in the atlas topology. This is part of the setting for $V_\alpha$, the closure of the curve (6) in $\mathbb P^1\times\mathbb P^1$, which the note introduces before Lemma 4.
--
--   **Formalization Note**: the point at infinity enters as the image of $\infty$ under Mathlib's bijection between `OnePoint ℂ` and the projective line.
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

theorem CurveSymmetry.affineLinePoint_range (p : ProjectiveLine) :
    p ∈ Set.range affineLinePoint ↔ p ≠ sphereProjectiveEquiv (∞ : Sphere) := by sorry
