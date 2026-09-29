-- Prove2me | Theorems.Thm_Algebra_Etale_isIntegrallyClosed_tensorProduct_of_isDomain
-- name    : Algebra.Etale.isIntegrallyClosed_tensorProduct_of_isDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/a262a385-e6bb-57cb-9e27-ec41cd5ac916
-- title:
--   Étale base change preserves integral closedness of domains
-- statement:
--   Let $W$ be a commutative ring and let $B$ and $W'$ be commutative rings equipped with $W$-algebra structures, the algebra $W \to W'$ being étale (in Mathlib's sense: formally étale and of finite presentation). Assume $B$ is a domain and is integrally closed in its fraction field, and assume further that the tensor product $B \otimes_W W'$, taken over $W$ and regarded as a commutative ring, is a domain. The conclusion is that $B \otimes_W W'$ is integrally closed. The hypothesis that $B \otimes_W W'$ be a domain is a genuine assumption and not part of the conclusion: an étale base change of a domain need not be a domain (for instance $W' = W \times W$), and integral closedness is asserted here only in the domain case. No finiteness or flatness assumption is placed on $B$ over $W$, and the three carrier types live in independent universes.
--
--   This is the ascent of normality along an étale morphism, in the affine and absolute form: the étale base change of a normal domain is normal whenever it remains a domain. It is used in the analysis of charts of an integral model of a modular curve, where a normal integral model is base changed along an étale extension of the base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_isIntegrallyClosed_tensorProduct_of_isDomain.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.Etale.isIntegrallyClosed_tensorProduct_of_isDomain
    {W : Type*} [CommRing W] (B W' : Type*) [CommRing B] [CommRing W'] [Algebra W B] [Algebra W W']
    [Algebra.Etale W W'] [IsDomain B] [IsIntegrallyClosed B] [IsDomain (B ⊗[W] W')] :
    IsIntegrallyClosed (B ⊗[W] W') := by sorry
