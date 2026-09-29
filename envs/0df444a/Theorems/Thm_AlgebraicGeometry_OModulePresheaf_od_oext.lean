-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_od_oext
-- name    : AlgebraicGeometry.OModulePresheaf.od_oext
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/1de38a94-1ec6-551c-acca-79ae36061995
-- title:
--   Alternating extension commutes with the Čech differential
-- statement:
--   Fix a commutative ring $R$, a scheme $V$ and a morphism $\pi : V \to \operatorname{Spec} R$, and let $F$ be an `OModulePresheaf` over $\pi$: an assignment of an abelian group $F.obj\,U$ to each open $U \subseteq V$, carrying an $R$-module structure and a $\Gamma(V,U)$-module structure which form a scalar tower along the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restriction maps $F.res : F.obj\,U' \to F.obj\,U$ for $U \le U'$ that are semilinear for restriction of sections, are the identity for $U = U'$, and compose. Let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $\iota$ together with opens $K.U\,i$, each affine, with $\bigsqcup_i K.U\,i = \top$. Let $n$ be a natural number and let $z$ be an $n$-cochain for $F$ and $K$, i.e. a family assigning to each strictly monotone index tuple $s \in K.Idx\,n$ an element of $F.obj$ of the intersection $\bigwedge_j K.U\,(s\,j)$. The assertion is that the project's differential `od` on ordered cochains applied to the alternating extension $F.oext\,K\,n\,z$ agrees with the alternating extension in degree $n+1$ of $F.d\,K\,n\,z$. Here `oext` is the $R$-linear map sending $z$ to the ordered cochain whose value at a tuple $t \in K.OIdx\,n$ is $\operatorname{sign}(\mathrm{Tuple.sort}\,t)$ times the restriction of $z$ at the sorted tuple `K.osort t` to the intersection $K.ointer\,t$ when $t$ is injective, and $0$ when $t$ has a repeated entry.
--
--   This is the statement that the alternating extension from strictly increasing Čech cochains to arbitrary (ordered) cochains is a morphism of complexes, the comparison underlying the classical identification of the ordered and alternating Čech complexes of a cover. It is used in the project's iterated Čech and Leray constructions, for instance in the comparison of the total and Čech augmentations and in the construction of homotopies relating cup products with the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_od_oext.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.od_oext
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.od K n (F.oext K n z) = F.oext K (n + 1) (F.d K n z) := by sorry
