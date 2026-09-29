-- Prove2me | Theorems.Thm_CuspidalType_not_isRoot_charpoly_torus
-- name    : CuspidalType.not_isRoot_charpoly_torus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/b75981da-e477-515f-b1ab-197b5dc54397
-- title:
--   Regular non-split torus elements have no eigenvalue in 𝔽_q
-- statement:
--   Let $q$ be a prime and let `GaloisField q 2` be the field with $q^2$ elements, viewed as a $\mathbb{Z}/q$-algebra. Fix a unit $\alpha$ of this field and assume that $\alpha$, regarded as an element of `GaloisField q 2`, does not lie in the image of the structure map $\mathbb{Z}/q \to$ `GaloisField q 2`, i.e. $\alpha \notin \mathbb{F}_q$. Write $T(\alpha) \in$ `GL2 q` $= \mathrm{GL}_2(\mathbb{Z}/q)$ for the image of $\alpha$ under `torus q`, the group homomorphism obtained from multiplication by $\alpha$ on `GaloisField q 2` as a $\mathbb{Z}/q$-linear endomorphism (`Algebra.lmul`), expressed as a $2\times 2$ matrix in the $\mathbb{Z}/q$-basis `quadBasis q` of `GaloisField q 2` indexed by `Fin 2` (which exists because the $\mathbb{Z}/q$-rank of `GaloisField q 2` is $2$), and then transported to units by `Units.map`. The assertion is that for every $x \in \mathbb{Z}/q$, the element $x$ is not a root of the characteristic polynomial of the underlying matrix of $T(\alpha)$ over $\mathbb{Z}/q$.
--
--   This is the standard fact that an element of the non-split torus of $\mathrm{GL}_2(\mathbb{F}_q)$ coming from $\alpha \in \mathbb{F}_{q^2} \setminus \mathbb{F}_q$ has characteristic polynomial equal to the (irreducible, quadratic) minimal polynomial of $\alpha$ over $\mathbb{F}_q$, so that such an element is elliptic: it has no eigenvalue in $\mathbb{F}_q$ and in particular is neither central nor split. It is used in the conjugacy-class bookkeeping for cuspidal representations of $\mathrm{GL}_2(\mathbb{F}_q)$ ([`CuspidalType.NV3Arch.sum_elliptic_eq`](thm.html#CuspidalType.NV3Arch.sum_elliptic_eq)) and in the vanishing of a twisted intertwining map ([`DrinfeldCurve.intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_isAlgClosed`](thm.html#DrinfeldCurve.intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_isAlgClosed)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_not_isRoot_charpoly_torus.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.not_isRoot_charpoly_torus (q : ℕ) [Fact q.Prime] {α : (GaloisField q 2)ˣ}
    (hα : (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))) (x : ZMod q) :
    ¬ ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x := by sorry
