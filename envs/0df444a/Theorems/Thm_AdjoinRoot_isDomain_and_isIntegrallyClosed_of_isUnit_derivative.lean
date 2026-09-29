-- Prove2me | Theorems.Thm_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative
-- name    : AdjoinRoot.isDomain_and_isIntegrallyClosed_of_isUnit_derivative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/1f4fd083-c72c-544e-ac6d-de42036006a5
-- title:
--   R[X]/(f) is a normal domain when f' is a unit
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and is integrally closed (in the sense of `IsIntegrallyClosed`: every element of its fraction field which is integral over $R$ lies in the image of $R$). Let $f \in R[X]$ be a monic polynomial which is irreducible as an element of the polynomial ring $R[X]$, and assume that the image of the formal derivative $f'$ under the quotient map $R[X] \to R[X]/(f)$ is a unit of $R[X]/(f)$. The conclusion is the conjunction of two assertions about the ring $A =$ `AdjoinRoot f`, i.e. the quotient $R[X]/(f)$: first, $A$ is an integral domain; second, $A$ is integrally closed, i.e. every element of the fraction field of $A$ that is integral over $A$ already comes from $A$. Note that the second component presupposes the first, so the statement is packaged as a conjunction rather than as two separate lemmas.
--
--   This is the standard normality statement for a standard étale extension of a normal domain: adjoining a root of a monic irreducible polynomial with invertible derivative preserves being an integrally closed domain. It is used in the proof of the criterion [`IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete`](thm.html#IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete), which recognises étaleness of a finite algebra over a complete local ring from a rank count.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial in

theorem AdjoinRoot.isDomain_and_isIntegrallyClosed_of_isUnit_derivative
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (f : R[X]) (hfm : f.Monic) (hfi : Irreducible f)
    (hu : IsUnit (AdjoinRoot.mk f (derivative f))) :
    IsDomain (AdjoinRoot f) ∧ IsIntegrallyClosed (AdjoinRoot f) := by sorry
