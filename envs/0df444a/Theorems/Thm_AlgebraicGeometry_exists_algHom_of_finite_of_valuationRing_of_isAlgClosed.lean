-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_algHom_of_finite_of_valuationRing_of_isAlgClosed
-- name    : AlgebraicGeometry.exists_algHom_of_finite_of_valuationRing_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/46b6716f-7dd9-5f66-9a40-a2376e79170b
-- title:
--   Sections of finite algebras over valuation rings
-- statement:
--   Let $R$ be a commutative ring that is an integral domain and a valuation ring, and suppose its fraction field $K = \mathrm{FractionRing}\,R$ is algebraically closed. Let $D$ be a commutative ring equipped with an $R$-algebra structure which is finite as an $R$-module, and assume that the base change $K \otimes_R D$ is nontrivial, i.e. $0 \neq 1$ in it, so that $D$ has nonzero generic fibre. The conclusion is that the type of $R$-algebra homomorphisms $D \to R$ is nonempty: there exists an $R$-algebra map $s : D \to R$. Thus a finite algebra over a valuation ring whose fraction field is algebraically closed admits an $R$-valued point as soon as its generic fibre is nonzero. Only the existence of such a section is asserted; no uniqueness or compatibility is claimed.
--
--   This is the standard statement that an $R$-point of a finite $R$-scheme can be found whenever the generic fibre is nonempty, over a valuation ring with algebraically closed fraction field (so $R$ is integrally closed and, for $R$ the ring of integers of a complete algebraically closed field, the relevant adic situation). It is used in the construction of the quotient datum for a flat proper tower in [`AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen`](thm.html#AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen), where points must be lifted along a finite projection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_algHom_of_finite_of_valuationRing_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicGeometry.exists_algHom_of_finite_of_valuationRing_of_isAlgClosed
    (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (hC : IsAlgClosed (FractionRing R))
    (D : Type) [CommRing D] [Algebra R D] [Module.Finite R D]
    (hD : Nontrivial (TensorProduct R (FractionRing R) D)) :
    Nonempty (D →ₐ[R] R) := by sorry
