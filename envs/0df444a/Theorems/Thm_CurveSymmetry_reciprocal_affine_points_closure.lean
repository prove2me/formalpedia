-- Prove2me | Theorems.Thm_CurveSymmetry_reciprocal_affine_points_closure
-- name    : CurveSymmetry.reciprocal_affine_points_closure
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:05.401257+00:00
-- url     : https://prove2.me/theorems/7e229344-30e9-4c30-893d-d8f0069ffe05
-- title:
--   Zariski closure of the curve $P_\alpha=0$ in the chart $(1/X,1/Y)$ of $\mathbb P^1\times\mathbb P^1$
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha\in\mathbb C$ be arbitrary. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ be the polynomial of equation (6). Near $(X,Y)=(\infty,\infty)$, use the chart of $\mathbb P^1\times\mathbb P^1$ with coordinates $(u,v)$, where $u=1/X$ and $v=1/Y$, and put $Q_\alpha(u,v)=u^m+v^m+uv\,(\bar\alpha u^m+\alpha v^m)$, which equals $u^{m+1}v^{m+1}P_\alpha(1/u,1/v)$. Let $\operatorname{Spec}\mathbb C[u,v]$ be the prime spectrum of the polynomial ring in the chart coordinates, with its Zariski topology; for $w\in\mathbb C^2$ let $\mathfrak m_w$ be the maximal ideal of the polynomials vanishing at $w$, and let $V(Q_\alpha)$ be the set of prime ideals containing $Q_\alpha$.
--
--   Then the closure of the points of the affine curve $P_\alpha=0$ off both coordinate axes, written in the chart coordinates, is the whole zero locus of $Q_\alpha$:
--
--   $$\overline{\bigl\{\mathfrak m_{(1/X,\,1/Y)}\ :\ (X,Y)\in\mathbb C^2,\ P_\alpha(X,Y)=0,\ X\ne0,\ Y\ne0\bigr\}}=V(Q_\alpha).$$
--
--   This is one of the chart computations behind $V_\alpha$, the closure of the curve (6) in $\mathbb P^1\times\mathbb P^1$, which the note introduces before Lemma 4: in the chart around the boundary point $(\infty,\infty)$, the closure of the affine curve is cut out by $Q_\alpha$. Gluing the charts into a global statement is a separate step.
--
--   **Formalization Note**: points of $\mathbb C^2$ are sent into the prime spectrum by $w\mapsto\mathfrak m_w$, the kernel of evaluation at $w$; the closure and the zero locus are taken in Mathlib's prime spectrum with its Zariski topology, non-closed points included.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/AffineChartImages.lean (C. Perassi)

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
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.reciprocal_affine_points_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure ((fun z : Fin 2 → ℂ => affineSpectrumPoint ![(z 0)⁻¹, (z 1)⁻¹]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 0 ≠ 0 ∧ z 1 ≠ 0}) =
      PrimeSpectrum.zeroLocus ({familyInfinityPolynomial m α} : Set BPoly) := by sorry
