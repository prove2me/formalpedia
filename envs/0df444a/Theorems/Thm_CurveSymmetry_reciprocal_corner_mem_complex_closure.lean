-- Prove2me | Theorems.Thm_CurveSymmetry_reciprocal_corner_mem_complex_closure
-- name    : CurveSymmetry.reciprocal_corner_mem_complex_closure
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:09.601531+00:00
-- url     : https://prove2.me/theorems/801a2393-bcf6-4a62-931f-89af8c42a0a3
-- title:
--   The corner $(\infty,\infty)$ lies in the Zariski closure of complex points of its chart curve with $uv\ne0$
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha\in\mathbb C$ be arbitrary. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ and $R_\alpha(u,v)=u^m+v^m+uv\,(\bar\alpha u^m+\alpha v^m)\in\mathbb C[u,v]$. For $uv\ne0$ one has $R_\alpha(u,v)=u^{m+1}v^{m+1}P_\alpha(1/u,1/v)$, so $R_\alpha$ is the equation of the curve $P_\alpha=0$ in the chart $u=1/X$, $v=1/Y$ around the point $(\infty,\infty)$ of $\mathbb P^1\times\mathbb P^1$. For $w\in\mathbb C^2$ let $\mathfrak m_w$ be the maximal ideal of the polynomials vanishing at $w$, a point of $\operatorname{Spec}\mathbb C[u,v]$, and let $V(R_\alpha)$ be the set of prime ideals containing $R_\alpha$.
--
--   Then, with the closure taken in the Zariski topology,
--
--   $$
--   \mathfrak m_{(0,0)}\in\overline{\bigl\{\mathfrak m_w:\ w=(w_0,w_1)\in\mathbb C^2,\ R_\alpha(w)=0,\ w_0\ne0,\ w_1\ne0\bigr\}}.
--   $$
--
--   The origin of this chart represents the point $(\infty,\infty)$ of $\mathbb P^1\times\mathbb P^1$, while at the approximating points both $X=1/w_0$ and $Y=1/w_1$ are finite. So $(\infty,\infty)$ lies in the Zariski closure of points of the affine curve $P_\alpha=0$, part of the description of the closure of the curve (6) in $\mathbb P^1\times\mathbb P^1$; the gluing of the charts is a separate step.
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

theorem CurveSymmetry.reciprocal_corner_mem_complex_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    affineSpectrumPoint ![0, 0] ∈
      closure (affineSpectrumPoint '' {v : Fin 2 → ℂ |
        eval v (familyInfinityPolynomial m α) = 0 ∧ v 0 ≠ 0 ∧ v 1 ≠ 0}) := by sorry
