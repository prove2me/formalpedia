-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ores_oext
-- name    : AlgebraicGeometry.OModulePresheaf.ores_oext
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/582dd86b-0184-585b-8e29-69f8c4682f95
-- title:
--   Restriction of the alternating extension is the identity
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi : V \to \operatorname{Spec} R$ a morphism, and let $F$ be an `OModulePresheaf` over $\pi$: an assignment $U \mapsto F.\mathrm{obj}\,U$ of an $R$-module to each open $U \subseteq V$ which is simultaneously a $\Gamma(V,U)$-module compatibly with the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, equipped with $R$-linear restriction maps $F.\mathrm{res}$ for $U \le U'$ that are semilinear for the presheaf restriction on sections and satisfy the identity and composition laws. Let $K$ be an ordered affine cover of $V$, i.e. a finite linearly ordered index type $\iota$ together with affine opens $K.U\,i$ whose supremum is $\top$, let $n \in \mathbb{N}$, and let $z$ be an $n$-cochain for $K$, that is, a family assigning to every strictly increasing tuple $s : \mathrm{Fin}(n+1) \to \iota$ an element of $F$ over $K.\mathrm{inter}\,s = \bigcap_j K.U(s_j)$. The conclusion is that $F.\mathrm{ores}\,K\,n\,(F.\mathrm{oext}\,K\,n\,z) = z$: forming the alternating ordered cochain $F.\mathrm{oext}$, whose value at an arbitrary tuple $t$ is $\operatorname{sign}(\mathrm{Tuple.sort}\,t)$ times the restriction of $z$ at the sorted tuple $K.\mathrm{osort}\,t$ when $t$ is injective and $0$ otherwise, and then restricting back along the inclusion of strictly increasing tuples into all tuples, returns $z$ unchanged.
--
--   This is the statement that the alternating extension map from increasing-chain Čech cochains to all-tuple (ordered) cochains is a section of the forgetful restriction map, so that the ordered and increasing Čech complexes of an ordered affine cover compute the same cochain classes. It is used in the Leray-type comparison `exists_dTot_eq_single_biAug_unitPullback_sub_single_id` and in the graded commutativity and pullback-compatibility statements `cls_mul_comm_graded` and `unitPullback_cup_sub_cup_unitPullback_mem_of_mem_ker` for cup products on these complexes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_ores_oext.lean

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

theorem AlgebraicGeometry.OModulePresheaf.ores_oext
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.ores K n (F.oext K n z) = z := by sorry
