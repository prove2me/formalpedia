-- Prove2me | Theorems.Thm_CuspidalType_mul_torus_eq_torus_mul_iff
-- name    : CuspidalType.mul_torus_eq_torus_mul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/b0a187f9-eb47-55d5-954d-93c77fb09265
-- title:
--   Centraliser of a regular non-split torus element in GL₂(𝔽_q)
-- statement:
--   Let $q$ be a prime and let `GaloisField q 2` be the field with $q^2$ elements, viewed as an algebra over `ZMod q`; fix the $\mathbb{F}_q$-basis `quadBasis q` of it indexed by `Fin 2`, obtained from the fact that its rank over $\mathbb{F}_q$ is $2$. Write `torus q` for the monoid homomorphism from $(\mathbb{F}_{q^2})^\times$ to the general linear group `GL2 q` $=\mathrm{GL}_2(\mathbb{F}_q)$ of $2\times 2$ invertible matrices over `ZMod q` obtained by taking units in the algebra homomorphism that sends $x\in\mathbb{F}_{q^2}$ to the matrix, in the basis `quadBasis q`, of the $\mathbb{F}_q$-linear map "multiplication by $x$". Let $\alpha$ be a unit of `GaloisField q 2` whose underlying element does not lie in the range of the structure map $\mathbb{F}_q \to \mathbb{F}_{q^2}$, i.e. $\alpha \notin \mathbb{F}_q$, and let $h \in \mathrm{GL}_2(\mathbb{F}_q)$. Then $h\,\mathrm{torus}_q(\alpha) = \mathrm{torus}_q(\alpha)\,h$ if and only if $h$ lies in the range of the homomorphism `torus q`.
--
--   This identifies the centraliser in $\mathrm{GL}_2(\mathbb{F}_q)$ of a regular element of the non-split (elliptic) Cartan subgroup with that Cartan subgroup itself, so that the non-split torus is its own centraliser and the conjugacy class of such an element has $q(q-1)$ elements. It is used in the computation [`CuspidalType.NV3Arch.sum_elliptic_eq`](thm.html#CuspidalType.NV3Arch.sum_elliptic_eq) of a sum over elliptic conjugacy classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_mul_torus_eq_torus_mul_iff.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.mul_torus_eq_torus_mul_iff (q : ℕ) [Fact q.Prime] {α : (GaloisField q 2)ˣ}
    (hα : (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))) (h : GL2 q) :
    h * torus q α = torus q α * h ↔ h ∈ (torus q).range := by sorry
