-- Prove2me | Theorems.Thm_CurveSymmetry_polynomial_rotation_bound
-- name    : CurveSymmetry.polynomial_rotation_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:05.150816+00:00
-- url     : https://prove2.me/theorems/47dbb889-6f14-4c40-8b30-dd676a672df2
-- title:
--   Polynomial rotation bound $N\le\max\{d,2d-4\}$ for non-radial, non-homogeneous polynomials fixed up to sign
-- statement:
--   Let $N\ge 0$ be an integer and let $\zeta\in\mathbb C$ be a primitive $N$-th root of unity, in the sense that $\zeta^N=1$ and $N$ divides every $k\in\mathbb N$ with $\zeta^k=1$. Let $P=\sum_{a,b\ge 0}p_{ab}X^aY^b\in\mathbb C[X,Y]$ be a polynomial of total degree $d=\deg P\ge 2$ such that:
--
--   1. $P$ is not radial: $p_{ab}\ne 0$ for some $(a,b)$ with $a\ne b$ (equivalently, $P$ is not a polynomial in $XY$);
--   2. for no integer $k\ge 2$ is $P$ homogeneous of degree $k$;
--   3. $P$ is fixed up to sign by the substitution $X\mapsto\zeta X$, $Y\mapsto\zeta^{-1}Y$: either $P(\zeta X,\zeta^{-1}Y)=P(X,Y)$ or $P(\zeta X,\zeta^{-1}Y)=-P(X,Y)$.
--
--   Then
--
--   $$
--   N\le\max\{d,\,2d-4\}.
--   $$
--
--   This isolates, as a statement about a single polynomial, the coefficient argument behind the rotation bound of Theorem 1, which rests on the weight identity (4) and the radial form (5). The two shapes that the note rules out using irreducibility and the hypothesis that the curve is not a circle, a polynomial in $XY$ and a homogeneous binary form, appear here as explicit hypotheses.
--
--   **Formalization Note**: primitive roots follow Mathlib's convention, so $N=0$ is allowed (no positive power of $\zeta$ equals $1$; for $\zeta=0$ the inverse is read as $0^{-1}=0$). The number $2d-4$ is a truncated difference of natural numbers, which is exact here because $d\ge 2$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 1, equation (5), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/RotationSupport.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.polynomial_rotation_bound {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) {P : BPoly} (hd : 2 ≤ P.totalDegree)
    (hnonradial : ∃ s ∈ P.support, s 0 ≠ s 1)
    (hhom : ∀ m : ℕ, 2 ≤ m → ¬ P.IsHomogeneous m)
    (hsign : rotate ζ P = P ∨ rotate ζ P = -P) :
    N ≤ max P.totalDegree (2 * P.totalDegree - 4) := by sorry
