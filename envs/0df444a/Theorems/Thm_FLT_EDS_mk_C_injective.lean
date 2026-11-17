-- Prove2me | Theorems.Thm_FLT_EDS_mk_C_injective
-- name    : FLT.EDS.mk_C_injective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:23.47519+00:00
-- url     : https://prove2.me/theorems/3987ede9-4918-48e4-8e3d-5ccf358a5439
-- title:
--   Polynomials in $X$ embed in the affine Weierstrass coordinate ring
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$. Write $A_W=R[X,Y]/(F_W)$ for its affine coordinate ring, let $C:R[X]→R[X][Y]$ regard a polynomial in $X$ as constant in $Y$, and let $π:R[X][Y]→A_W$ be the quotient map. Then the map $p↦π(C(p))$ is injective: $$π(C(p))=π(C(q))⇒p=q.$$ This permits identities in the coordinate ring to be reflected back to ordinary division polynomials in $R[X]$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

open Polynomial WeierstrassCurve
open scoped Classical
variable {R : Type*} [CommRing R]

theorem FLT.EDS.mk_C_injective (W : WeierstrassCurve R) :
    Function.Injective (fun p : R[X] => Affine.CoordinateRing.mk W (Polynomial.C p)) := by sorry
