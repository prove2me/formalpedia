-- Prove2me | Theorems.Thm_CurveSymmetry_mixed_corner_mem_complex_closure
-- name    : CurveSymmetry.mixed_corner_mem_complex_closure
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:45.844986+00:00
-- url     : https://prove2.me/theorems/fd4a4060-74a2-4bb2-8b68-68cfacdebb22
-- title:
--   The origin of a mixed chart lies in the Zariski closure of complex points of the chart curve with $u\ne0$
-- statement:
--   Let $m\ge1$ be an integer, let $a,b\in\mathbb C$ be arbitrary, and let $Q_{a,b}(u,y)=a\,u+y+b\,u^{m+1}y^m+u^my^{m+1}\in\mathbb C[u,y]$. With $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$, the choice $(a,b)=(\alpha,\bar\alpha)$ gives the polynomial equal to $u^{m+1}P_\alpha(1/u,y)$ for $u\ne0$, the equation of the curve $P_\alpha=0$ in the chart $u=1/X$ near the boundary point $(\infty,0)$ of $\mathbb P^1\times\mathbb P^1$; the choice $(a,b)=(\bar\alpha,\alpha)$ gives the analogous equation near $(0,\infty)$, with the two coordinates exchanged. For $v\in\mathbb C^2$ let $\mathfrak m_v$ be the maximal ideal of the polynomials vanishing at $v$, a point of $\operatorname{Spec}\mathbb C[u,y]$.
--
--   Then, with the closure taken in the Zariski topology of $\operatorname{Spec}\mathbb C[u,y]$,
--
--   $$
--   \mathfrak m_{(0,0)}\in\overline{\bigl\{\mathfrak m_v:\ v=(v_0,v_1)\in\mathbb C^2,\ Q_{a,b}(v)=0,\ v_0\ne0\bigr\}}.
--   $$
--
--   The approximating points are complex points of the chart curve at which $X=1/v_0$ is finite; for $(a,b)=(\alpha,\bar\alpha)$ they correspond to the points $(1/v_0,v_1)$ of the affine curve $P_\alpha=0$. So the corner represented by the origin lies in the Zariski closure of points of the affine curve, as asserted for the closure of the curve (6) in $\mathbb P^1\times\mathbb P^1$.
--
--   **Formalization Note**: points of $\operatorname{Spec}\mathbb C[u,y]$ are elements of `PrimeSpectrum (MvPolynomial (Fin 2) ℂ)` with Mathlib's Zariski topology, $u$ and $y$ are the variables `X 0` and `X 1`, and $\mathfrak m_v$ is the kernel of evaluation at $v$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/MixedCornerClosure.lean (C. Perassi)

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

theorem CurveSymmetry.mixed_corner_mem_complex_closure {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    affineSpectrumPoint ![0, 0] ∈
      closure (affineSpectrumPoint '' {v : Fin 2 → ℂ |
        eval v (familyMixedPolynomial m a b) = 0 ∧ v 0 ≠ 0}) := by sorry
