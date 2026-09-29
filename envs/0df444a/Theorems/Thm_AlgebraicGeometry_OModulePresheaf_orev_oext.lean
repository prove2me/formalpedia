-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_orev_oext
-- name    : AlgebraicGeometry.OModulePresheaf.orev_oext
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/8dc91163-395e-56d2-8d52-3ddc567341f3
-- title:
--   Alternating extension is invariant under index reversal
-- statement:
--   Fix a commutative ring $R$, a scheme $V$ and a morphism $\pi : V \to \operatorname{Spec} R$. Let $F$ be an `OModulePresheaf` for $\pi$, that is: an assignment $U \mapsto F.obj(U)$ on the opens of $V$ of $R$-modules which are simultaneously $\Gamma(V,U)$-modules compatibly with the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restriction maps $F.res : F.obj(U') \to F.obj(U)$ for $U \le U'$ that are semilinear for restriction of sections, reflexive and transitive. Let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type $\iota$, opens $U_i$ with each $U_i$ affine and $\bigsqcup_i U_i = \top$. Let $n$ be a natural number and let $z$ be a cochain of degree $n$, i.e. a family assigning to each increasing index tuple $s \in K.Idx\,n$ an element of $F.obj\bigl(\bigwedge_j U_{s(j)}\bigr)$. The conclusion is the identity $F.orev\,K\,n\,(F.oext\,K\,n\,z) = F.oext\,K\,n\,z$, where $F.oext$ sends $z$ to the ordered cochain whose value at a tuple $t \in K.OIdx\,n$ (a family of indices indexed by $\mathrm{Fin}(n+1)$) is the sign of the sorting permutation of $t$ times the restriction of $z$ at the sorted tuple $K.osort\,t$ when $t$ is injective and is $0$ otherwise, and where $F.orev$ multiplies by $(-1)^{n(n+1)/2}$ and restricts the value at the reversed tuple $t \circ \mathrm{Fin.rev}$. Thus alternating cochains obtained by extension are fixed by the signed reversal operator.
--
--   This is the combinatorial compatibility, in the ordered Čech complex attached to a finite ordered affine cover, between the alternating extension of ordered cochains and the reversal of the index tuple twisted by $(-1)^{n(n+1)/2}$. It is used in the proof of graded commutativity of the cup product on the resulting Čech cohomology classes, [`AlgebraicGeometry.OModulePresheaf.cls_mul_comm_graded`](thm.html#AlgebraicGeometry.OModulePresheaf.cls_mul_comm_graded).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_orev_oext.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechReversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.orev_oext
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.orev K n (F.oext K n z) = F.oext K n z := by sorry
