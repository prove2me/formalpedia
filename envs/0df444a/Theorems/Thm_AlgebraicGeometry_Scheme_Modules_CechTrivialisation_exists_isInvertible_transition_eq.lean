-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq
-- name    : AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_isInvertible_transition_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/5244ce5d-18c7-54d4-be7e-9808bb8794f4
-- title:
--   Invertible module with prescribed Čech transition cocycle
-- statement:
--   Let $Y$ be a scheme and let $\mathcal V$ be an ordered affine cover of $Y$: a finite linearly ordered index type $\iota$ together with opens $U_a$ ($a\in\iota$), each affine, whose supremum is $\top$. For $i\in\mathbb N$ write $\mathcal V.\mathrm{Idx}\,i$ for the strictly monotone maps $\mathrm{Fin}(i+1)\to\iota$ and, for such an $s$, put $\mathcal V.\mathrm{inter}\,s=\bigwedge_j U_{s(j)}$. Given two families $u,u'$ assigning to each $s\in\mathcal V.\mathrm{Idx}\,1$ (that is, each pair $a<b$) a section of $\Gamma(Y,\mathcal V.\mathrm{inter}\,s)$, assume $u_s\,u'_s=1$ for all $s$, and assume the cocycle identity on triples: for every $r\in\mathcal V.\mathrm{Idx}\,2$ (that is, $a<b<c$), restricting along $\mathcal V.\mathrm{inter}\,r\le\mathcal V.\mathrm{inter}(\mathcal V.\mathrm{face}\,r\,j)$ one has $u_{\mathrm{face}\,r\,2}\cdot u_{\mathrm{face}\,r\,0}=u_{\mathrm{face}\,r\,1}$, the faces omitting the last, first and middle index respectively. Then there exists an $\mathcal O_Y$-module $\mathcal L$ (an object of `Y.Modules`) which is invertible in the sense that every point of $Y$ has an open neighbourhood $U$ for which the pullback of $\mathcal L$ along $U\hookrightarrow Y$ is isomorphic to the unit module on $U$, together with a Čech trivialisation $\tau$ of $\mathcal L$ on $\mathcal V$ — a family of isomorphisms of the pullback of $\mathcal L$ to $U_a$ with the unit module on $U_a$, one for each $a\in\iota$ — whose transition sections are exactly the given ones: $\tau.\mathrm{transition}\,s=u_s$ for every $s\in\mathcal V.\mathrm{Idx}\,1$, where $\tau.\mathrm{transition}\,s$ is the section of $\Gamma(Y,\mathcal V.\mathrm{inter}\,s)$ obtained by evaluating at $1$ the automorphism of the unit module on $\mathcal V.\mathrm{inter}\,s$ given by the inverse of the restriction of $\tau$ at the first index followed by the restriction at the second.
--
--   This is the gluing half of the Čech description of the Picard group: a multiplicative $1$-cocycle of units on an ordered affine cover, indexed only by increasing pairs and triples, is realised as the family of transition sections of an invertible module with a chosen trivialisation. It is used in the construction of line bundles from Picard obstruction and deformation cocycles over small extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq.lean

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

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_isInvertible_transition_eq
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover)
    (u u' : ∀ s : 𝒱.Idx 1, Γ(Y, 𝒱.inter s)) (huu' : ∀ s : 𝒱.Idx 1, u s * u' s = 1)
    (hcoc : ∀ r : 𝒱.Idx 2,
      (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 2)).op).hom (u (𝒱.face r 2)) *
          (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 0)).op).hom (u (𝒱.face r 0)) =
        (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 1)).op).hom (u (𝒱.face r 1))) :
    ∃ 𝓛 : Y.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      ∃ τ : Scheme.Modules.CechTrivialisation 𝒱 𝓛, ∀ s : 𝒱.Idx 1, τ.transition s = u s := by sorry
