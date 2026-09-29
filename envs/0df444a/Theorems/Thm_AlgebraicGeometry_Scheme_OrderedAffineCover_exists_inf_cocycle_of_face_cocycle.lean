-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_inf_cocycle_of_face_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/115f04a5-7a01-5e8a-905e-fbcfba5d3349
-- title:
--   From strictly increasing to all ordered pairs for unit cocycles
-- statement:
--   Let $Y$ be a scheme and let $\mathcal V$ be an `OrderedAffineCover` of $Y$: a finite linearly ordered index type $\iota$ together with opens $U_a \subseteq Y$ ($a \in \iota$), each affine, whose supremum is $\top$. For $i \in \mathbb N$, the index type $\mathcal V.\mathrm{Idx}\,i$ consists of strictly monotone maps $s : \mathrm{Fin}(i+1) \to \iota$, and $\mathcal V.\mathrm{inter}\,s = \bigwedge_j U_{s(j)}$; for $s \in \mathcal V.\mathrm{Idx}(i+1)$ and $j$, the face $\mathcal V.\mathrm{face}\,s\,j$ is $s$ composed with the $j$-th `succAbove` map, i.e. $s$ with its $j$-th entry deleted. Assume given sections $u_s, u'_s \in \Gamma(Y, \mathcal V.\mathrm{inter}\,s)$ for every strictly increasing pair $s \in \mathcal V.\mathrm{Idx}\,1$ with $u_s u'_s = 1$, and assume that for every strictly increasing triple $r \in \mathcal V.\mathrm{Idx}\,2$ the cocycle identity holds on $\mathcal V.\mathrm{inter}\,r$ after restriction along the inclusions $\mathcal V.\mathrm{inter}\,r \le \mathcal V.\mathrm{inter}(\mathcal V.\mathrm{face}\,r\,j)$: the product of the restrictions of $u$ at the faces $2$ and $0$ of $r$ equals the restriction of $u$ at the face $1$. Then there exists a family $W_{ab} \in \Gamma(Y, U_a \wedge U_b)$ indexed by all ordered pairs $(a,b) \in \iota \times \iota$ such that $W_{aa} = 1$, each $W_{ab}$ is a unit, for all $a,b,c$ the restrictions to $U_a \wedge U_b \wedge U_c$ satisfy $W_{ab} W_{bc} = W_{ac}$, and for every strictly increasing pair $s$ the restriction of $W_{s(0)s(1)}$ to $\mathcal V.\mathrm{inter}\,s$ along $\mathcal V.\mathrm{inter}\,s \le U_{s(0)} \wedge U_{s(1)}$ equals $u_s$.
--
--   This is the comparison between Čech cochains on strictly increasing simplices of an ordered cover and cochains on all tuples, in the multiplicative form for $1$-cocycles of units: a unit cocycle given only on increasing pairs and triples is extended to a transition system defined for every ordered pair, normalised along the diagonal. It is used by [`AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_isInvertible_transition_eq`](thm.html#AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_isInvertible_transition_eq) to produce invertible transition data on all pairwise intersections of the cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_inf_cocycle_of_face_cocycle
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover)
    (u u' : ∀ s : 𝒱.Idx 1, Γ(Y, 𝒱.inter s)) (huu' : ∀ s : 𝒱.Idx 1, u s * u' s = 1)
    (hcoc : ∀ r : 𝒱.Idx 2,
      (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 2)).op).hom (u (𝒱.face r 2)) *
          (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 0)).op).hom (u (𝒱.face r 0)) =
        (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 1)).op).hom (u (𝒱.face r 1))) :
    ∃ W : ∀ a b : 𝒱.ι, Γ(Y, 𝒱.U a ⊓ 𝒱.U b),
      (∀ a : 𝒱.ι, W a a = 1) ∧ (∀ a b : 𝒱.ι, IsUnit (W a b)) ∧
      (∀ a b c : 𝒱.ι,
        (Y.presheaf.map (homOfLE (inf_le_left : 𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U b)).op).hom (W a b) *
            (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
              𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U b ⊓ 𝒱.U c)).op).hom (W b c) =
          (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U c)).op).hom (W a c)) ∧
      (∀ s : 𝒱.Idx 1,
        (Y.presheaf.map (homOfLE (le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1) :
          𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1))).op).hom (W (s.1 0) (s.1 1)) = u s) := by sorry
