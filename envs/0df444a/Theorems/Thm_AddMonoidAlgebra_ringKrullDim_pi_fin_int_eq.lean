-- Prove2me | Theorems.Thm_AddMonoidAlgebra_ringKrullDim_pi_fin_int_eq
-- name    : AddMonoidAlgebra.ringKrullDim_pi_fin_int_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/52e95a33-03a5-5b2d-b4b5-691afd221ff4
-- title:
--   Krull dimension of κ[ℤ^t] equals t
-- statement:
--   For an arbitrary type $\kappa$ carrying a field structure and an arbitrary natural number $t$, the theorem asserts an equality of Krull dimensions in `WithBot ℕ∞`: the ring `ringKrullDim` of the additive monoid algebra of $\kappa$ over the additive group $\mathrm{Fin}\ t \to \mathbb{Z}$ equals the image of $t$ under the canonical coercion $\mathbb{N} \to$ `WithBot ℕ∞`. Here the additive monoid algebra is the $\kappa$-algebra of finitely supported functions from $\mathrm{Fin}\ t \to \mathbb{Z}$ to $\kappa$ with convolution product, i.e. the Laurent polynomial ring $\kappa[T_0^{\pm 1},\dots,T_{t-1}^{\pm 1}]$ in $t$ variables, written with the index group in the function-type spelling $\mathrm{Fin}\ t \to \mathbb{Z}$ rather than as an abstract free abelian group of rank $t$. No hypothesis is imposed on $\kappa$ beyond being a field, and none on $t$; in particular the case $t = 0$ is included, where the assertion is that a field has Krull dimension $0$.
--
--   This is the dimension formula for the coordinate ring of the split torus $\mathbb{G}_m^t$ over a field, equivalently the statement that the Laurent polynomial ring in $t$ variables over a field has Krull dimension $t$. It is used in the study of Hopf algebras that are locally standard smooth of a given relative dimension, where the rank of the group-like part has to be compared with the dimension of the ambient algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidAlgebra_ringKrullDim_pi_fin_int_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddMonoidAlgebra.ringKrullDim_pi_fin_int_eq (κ : Type*) [Field κ] (t : ℕ) :
    ringKrullDim (AddMonoidAlgebra κ (Fin t → ℤ)) = t := by sorry
