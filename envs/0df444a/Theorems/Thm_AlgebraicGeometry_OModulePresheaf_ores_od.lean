-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ores_od
-- name    : AlgebraicGeometry.OModulePresheaf.ores_od
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/8968083c-d9d0-516c-9492-23817a25d21d
-- title:
--   Restriction to increasing tuples is a cochain map
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi : V \to \operatorname{Spec} R$ a morphism. Let $F$ be an `OModulePresheaf` for $\pi$: data assigning to every open $U \subseteq V$ a module `F.obj U` which is simultaneously an $R$-module and a $\Gamma(V,U)$-module, compatibly for the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restriction maps $\mathrm{res}\,h : F.obj\,U' \to F.obj\,U$ for $U \le U'$ which are semilinear for restriction of sections ($\mathrm{res}\,h\,(a \cdot x) = (a|_U) \cdot \mathrm{res}\,h\,x$), are the identity for $h = \mathrm{le\_refl}\,U$, and compose. Let $K$ be an `OrderedAffineCover` of $V$: a finite linearly ordered index type $\iota$ together with opens $U_i$, each affine, with $\bigsqcup_i U_i = \top$. For $n \in \mathbb{N}$, an ordered $n$-cochain is a family $c$ assigning to every tuple $t : \mathrm{Fin}(n+1) \to \iota$ an element of $F.obj\,(\bigwedge_j U_{t(j)})$, and `F.ores K n` is the $R$-linear map sending such a family to its subfamily indexed by the increasing tuples $s \in K.Idx\,n$, a cochain in the sense of `F.cochain K n`. The assertion is that for every ordered $n$-cochain $c$ one has $\mathrm{ores}_{n+1}(\mathrm{od}_n\,c) = \mathrm{d}_n(\mathrm{ores}_n\,c)$, where $\mathrm{od}$ and $\mathrm{d}$ are the alternating-sum Čech differentials on ordered and on increasing cochains respectively.
--
--   This is the statement that restriction from the full (ordered) Čech complex of the cover to the subcomplex of increasing tuples is a morphism of complexes, the comparison underlying the standard identification of the two Čech complexes. It is used in the treatment of cup products and graded commutativity of classes (`cls_mul_comm_graded`) and in the comparison of pullbacks of cup products with cup products of pullbacks (`unitPullback_cup_sub_cup_unitPullback_mem_of_mem_ker`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_ores_od.lean

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

theorem AlgebraicGeometry.OModulePresheaf.ores_od
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (c : F.ocochain K n) :
    F.ores K (n + 1) (F.od K n c) = F.d K n (F.ores K n c) := by sorry
