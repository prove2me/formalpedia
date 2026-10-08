-- Prove2me | Theorems.Thm_CurveSymmetry_hasMultiplicityAt_unique
-- name    : CurveSymmetry.hasMultiplicityAt_unique
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:15.31828+00:00
-- url     : https://prove2.me/theorems/e3b5289c-3ed3-4591-848b-572fa569f854
-- title:
--   The multiplicity of a plane curve equation at a point is well defined
-- statement:
--   Let $P\in\mathbb{C}[X,Y]$, let $(x,y)\in\mathbb{C}^2$, and let $\mathfrak{m}=(X-x,\,Y-y)$ be the maximal ideal of $\mathbb{C}[X,Y]$ of polynomials vanishing at $(x,y)$. Say that $P$ has multiplicity $n\in\mathbb{N}$ at $(x,y)$ if $P\in\mathfrak{m}^{n}$ and $P\notin\mathfrak{m}^{n+1}$.
--
--   If $P$ has multiplicity $n$ and also multiplicity $k$ at $(x,y)$, then $n=k$:
--
--   $$P\in\mathfrak{m}^{n}\setminus\mathfrak{m}^{n+1}\ \text{ and }\ P\in\mathfrak{m}^{k}\setminus\mathfrak{m}^{k+1}\quad\Longrightarrow\quad n=k.$$
--
--   So the multiplicity at a point, when defined, is a single number. This is the notion of multiplicity behind the ordinary $m$-fold points in Lemma 4 of the note and behind the simple points of the chart equations of $V_\alpha$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/OrdinaryMultiplePoints.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Mathlib.Algebra.MvPolynomial.Funext
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
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
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
open MvPolynomial

theorem CurveSymmetry.hasMultiplicityAt_unique {P : BPoly} {x y : ℂ} {n k : ℕ}
    (hn : HasMultiplicityAt P x y n) (hk : HasMultiplicityAt P x y k) : n = k := by sorry
