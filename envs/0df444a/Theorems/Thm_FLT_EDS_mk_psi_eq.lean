-- Prove2me | Theorems.Thm_FLT_EDS_mk_psi_eq
-- name    : FLT.EDS.mk_psi_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:21.984261+00:00
-- url     : https://prove2.me/theorems/c5f1bc6c-64aa-4f6d-85fb-9e4441c6585e
-- title:
--   A division polynomial splits into its normalized part and the parity factor
-- statement:
--   Let $R$ be a commutative ring, let $W$ be a Weierstrass curve, and let $n∈ℤ$. In the affine coordinate ring of $W$, write $[ψ_n]$ for the class of the full division polynomial, $[Ψ̃_n]$ for the class of the normalized one-variable polynomial, and set $ε_n=[ψ_2]$ when $n$ is even and $ε_n=1$ when $n$ is odd. Then $$[ψ_n]=[Ψ̃_n]ε_n.$$ This isolates the parity-dependent $ψ_2$ factor needed to translate Ward recurrences to one-variable division polynomials.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

open Polynomial WeierstrassCurve
open scoped Classical
variable {R : Type*} [CommRing R]

theorem FLT.EDS.mk_psi_eq (W : WeierstrassCurve R) (n : ℤ) :
    Affine.CoordinateRing.mk W (W.ψ n)
      = Affine.CoordinateRing.mk W (Polynomial.C (W.preΨ n))
          * (if Even n then Affine.CoordinateRing.mk W W.ψ₂ else 1) := by sorry
