-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_res_opair
-- name    : AlgebraicGeometry.OModulePresheaf.res_opair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/48a516c4-5341-5972-9d4a-92fd9cadac8e
-- title:
--   Pairing is compatible with enlarging the ambient tuple
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme with a morphism $\pi : V \to \operatorname{Spec} R$, and let $F$ be an `OModulePresheaf` over $\pi$: an assignment of an $R$-module and $\Gamma(V,U)$-module $F.obj(U)$ to each open $U \subseteq V$, compatible in the sense of a scalar tower, together with $R$-linear restriction maps $F.res : F.obj(U') \to F.obj(U)$ for $U \le U'$ that are semilinear for the structure sheaf restrictions and satisfy the identity and composition laws. Let $K$ be an ordered affine cover of $V$, i.e. a finite linearly ordered index type $\iota$ together with affine opens $U_i$ whose supremum is $\top$. For $m \in \mathbb{N}$ put $\mathrm{OIdx}\,m = (\mathrm{Fin}(m+1) \to \iota)$, and for a tuple $t$ write $\mathrm{ointer}\,t = \bigsqcap_j U_{t(j)}$. Let $t \in \mathrm{OIdx}\,k$ and $t' \in \mathrm{OIdx}\,k'$ satisfy $\mathrm{OSub}\,t'\,t$, i.e. every entry of $t'$ occurs among the entries of $t$, so that $\mathrm{ointer}\,t \le \mathrm{ointer}\,t'$. Let $c$ be an $n$-cochain, i.e. a family $c(u) \in F.obj(\mathrm{ointer}\,u)$ indexed by $u \in \mathrm{OIdx}\,n$, and let $x : \mathrm{OIdx}\,n \to_{\mathrm{f}} \mathbb{Z}$ be a finitely supported integer chain all of whose support tuples $u$ satisfy $\mathrm{OSub}\,u\,t'$. Here $\mathrm{opair}\,s\,n\,c$ denotes the $\mathbb{Z}$-linear map sending $x$ to $\sum_u x(u)\cdot \mathrm{oresTo}\,s\,u\,(c(u))$, where $\mathrm{oresTo}\,s\,u$ is the restriction $F.obj(\mathrm{ointer}\,u) \to F.obj(\mathrm{ointer}\,s)$ if $\mathrm{OSub}\,u\,s$ holds and $0$ otherwise. The conclusion is that restricting $\mathrm{opair}\,t'\,n\,c\,x$ along $\mathrm{ointer}\,t \le \mathrm{ointer}\,t'$ gives $\mathrm{opair}\,t\,n\,c\,x$.
--
--   This is the compatibility of the cochain–chain pairing with passage from a tuple $t'$ to a larger tuple $t$, the support hypothesis guaranteeing that no term of the pairing is annihilated by the convention that $\mathrm{oresTo}$ vanishes off the $\mathrm{OSub}$ relation. It is used in the ordered Čech machinery, namely in [`AlgebraicGeometry.OModulePresheaf.sub_oext_ores_mem_of_od_eq_zero`](thm.html#AlgebraicGeometry.OModulePresheaf.sub_oext_ores_mem_of_od_eq_zero), where faces of a tuple are drawn from that tuple and their pairings must be compared on a common open.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_res_opair.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.res_opair
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {k k' : ℕ} (t : K.OIdx k) (t' : K.OIdx k') (htt : K.OSub t' t)
    (n : ℕ) (c : F.ocochain K n) (x : K.OCh n) (hx : ∀ u ∈ x.support, K.OSub u t') :
    F.res (K.ointer_le_ointer_of_oSub htt) (F.opair K t' n c x) = F.opair K t n c x := by sorry
