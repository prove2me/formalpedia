-- Prove2me | Theorems.Thm_CurveSymmetry_anti_even_order
-- name    : CurveSymmetry.anti_even_order
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:26.92161+00:00
-- url     : https://prove2.me/theorems/5748685a-0e39-47a9-8483-6ec7b38e5b5c
-- title:
--   A nonzero polynomial negated by a rotation of order $N$ forces $N$ to be even
-- statement:
--   Let $N\ge 0$ be an integer and let $\zeta\in\mathbb C$ be a primitive $N$-th root of unity, in the sense that $\zeta^N=1$ and $N$ divides every $k\in\mathbb N$ with $\zeta^k=1$. Let $P\in\mathbb C[X,Y]$ be a nonzero polynomial that changes sign under the substitution $X\mapsto\zeta X$, $Y\mapsto\zeta^{-1}Y$:
--
--   $$
--   P(\zeta X,\zeta^{-1}Y)=-P(X,Y).
--   $$
--
--   Then $N$ is even.
--
--   When $N\ge 1$, so that $|\zeta|=1$, the substitution is, in the coordinates $X=z$, $Y=\bar z$ of the note, the pullback of the equation by the rotation $z\mapsto\zeta z$. In the proof of Theorem 1 this is the step showing that, when a generator of the rotation group acts on the equation by the sign $\varepsilon=-1$ of (4), its order $N=2m$ is even.
--
--   **Formalization Note**: primitive roots follow Mathlib's convention, so $N=0$ is allowed; it means that no positive power of $\zeta$ equals $1$. The inverse $\zeta^{-1}$ is the field inverse with $0^{-1}=0$, which matters only when $N=0$ and $\zeta=0$.
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

theorem CurveSymmetry.anti_even_order {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {P : BPoly}
    (hP : P ≠ 0) (hanti : rotate ζ P = -P) : Even N := by sorry
