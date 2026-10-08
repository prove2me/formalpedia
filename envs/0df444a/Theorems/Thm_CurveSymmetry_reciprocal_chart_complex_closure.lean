-- Prove2me | Theorems.Thm_CurveSymmetry_reciprocal_chart_complex_closure
-- name    : CurveSymmetry.reciprocal_chart_complex_closure
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:04.980458+00:00
-- url     : https://prove2.me/theorems/b6e881df-852a-41d9-bbdf-1d9bd967d6be
-- title:
--   Complex points with $uv\ne0$ are Zariski dense in the chart curve of $P_\alpha=0$ at $(\infty,\infty)$
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha\in\mathbb C$ be arbitrary. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ and $R_\alpha(u,v)=u^m+v^m+uv\,(\bar\alpha u^m+\alpha v^m)\in\mathbb C[u,v]$. For $uv\ne0$ one has $R_\alpha(u,v)=u^{m+1}v^{m+1}P_\alpha(1/u,1/v)$, so $R_\alpha$ is the equation of the curve $P_\alpha=0$ in the chart $u=1/X$, $v=1/Y$ around the point $(\infty,\infty)$ of $\mathbb P^1\times\mathbb P^1$. For $w\in\mathbb C^2$ let $\mathfrak m_w$ be the maximal ideal of the polynomials vanishing at $w$, a point of $\operatorname{Spec}\mathbb C[u,v]$, and let $V(R_\alpha)$ be the set of prime ideals containing $R_\alpha$.
--
--   Then, in the Zariski topology of $\operatorname{Spec}\mathbb C[u,v]$,
--
--   $$
--   \overline{\bigl\{\mathfrak m_w:\ w=(w_0,w_1)\in\mathbb C^2,\ R_\alpha(w)=0,\ w_0\ne0,\ w_1\ne0\bigr\}}=V(R_\alpha).
--   $$
--
--   Neither irreducibility nor smoothness of the curve $R_\alpha=0$ is assumed, and $\alpha$ may be real. The points with $w_0w_1\ne0$ correspond to the points $(1/w_0,1/w_1)$ of the affine curve $P_\alpha=0$ with $XY\ne0$, so the whole chart curve lies in the closure of the affine curve. The formalization uses this when the four standard charts are glued, to show that the zero set of the bihomogeneous equation lies in the closure of the curve (6) in $\mathbb P^1\times\mathbb P^1$.
--
--   **Formalization Note**: points of $\operatorname{Spec}\mathbb C[u,v]$ are elements of `PrimeSpectrum (MvPolynomial (Fin 2) ℂ)` with Mathlib's Zariski topology, $u$ and $v$ are the variables `X 0` and `X 1`, and $\mathfrak m_w$ is the kernel of evaluation at $w$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/ReciprocalCornerClosure.lean (C. Perassi)

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

theorem CurveSymmetry.reciprocal_chart_complex_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure (affineSpectrumPoint '' {v : Fin 2 → ℂ |
      eval v (familyInfinityPolynomial m α) = 0 ∧ v 0 ≠ 0 ∧ v 1 ≠ 0}) =
      PrimeSpectrum.zeroLocus ({familyInfinityPolynomial m α} : Set BPoly) := by sorry
