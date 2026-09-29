-- Prove2me | Theorems.Thm_Algebra_norm_one_tmul_eq_algebraMap_norm
-- name    : Algebra.norm_one_tmul_eq_algebraMap_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/00cdaf10-6460-5a29-9082-00f45e49c47c
-- title:
--   Base change of the algebra norm
-- statement:
--   Let $K$ be a commutative ring and $L$ a ring equipped with a $K$-algebra structure such that $L$ is free and finite as a $K$-module, and let $K'$ be a commutative ring equipped with a $K$-algebra structure. For every $x \in L$, the norm of the element $1 \otimes_K x$ of the $K'$-algebra $K' \otimes_K L$, taken relative to $K'$, equals the image under the structure map $K \to K'$ of the norm of $x$ relative to $K$: $$\mathrm{N}_{K' \otimes_K L / K'}(1 \otimes x) = \mathrm{algebraMap}\,(\mathrm{N}_{L/K}(x)).$$ Here the norm of an element of a finite free algebra is, as in Mathlib, the determinant of the $K$-linear (respectively $K'$-linear) endomorphism given by left multiplication by that element. Note that $L$ is not assumed commutative; only $K$ and $K'$ are commutative rings, and no further hypothesis (such as flatness, faithfulness, or an injectivity assumption on $K \to K'$) is imposed.
--
--   This is the standard compatibility of the algebra norm with extension of scalars, the norm form of a finite free algebra being stable under base change. It is used in the proof of [`Algebra.norm_algebraMap_eq_of_isPushout_of_isFractionRing`](thm.html#Algebra.norm_algebraMap_eq_of_isPushout_of_isFractionRing), where $K \subseteq K'$ are fraction fields and the base change identifies $K' \otimes_K L$ with the corresponding function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_norm_one_tmul_eq_algebraMap_norm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Algebra.norm_one_tmul_eq_algebraMap_norm
    {K : Type u} [CommRing K] {L : Type v} [Ring L] [Algebra K L] [Module.Free K L] [Module.Finite K L]
    (K' : Type w) [CommRing K'] [Algebra K K'] (x : L) :
    Algebra.norm K' ((1 : K') ⊗ₜ[K] x : K' ⊗[K] L) = algebraMap K K' (Algebra.norm K x) := by sorry
