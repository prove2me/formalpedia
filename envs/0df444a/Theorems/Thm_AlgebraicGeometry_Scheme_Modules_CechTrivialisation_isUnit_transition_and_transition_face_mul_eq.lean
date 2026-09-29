-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_isUnit_transition_and_transition_face_mul_eq
-- name    : AlgebraicGeometry.Scheme.Modules.CechTrivialisation.isUnit_transition_and_transition_face_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/18787e38-a971-5ed2-a7b0-f9b8b0e640bf
-- title:
--   Transition sections are units and satisfy the Čech cocycle identity
-- statement:
--   Let $Y$ be a scheme, let $\mathcal V$ be an ordered affine cover of $Y$ — a finite linearly ordered index type $\iota$ together with opens $U_a \subseteq Y$, each affine, whose supremum is $\top$ — let $\mathcal M$ be an $\mathcal O_Y$-module, and let $\tau$ be a Čech trivialisation of $\mathcal M$ on $\mathcal V$, i.e. a family of isomorphisms $\tau_a$ from the pullback of $\mathcal M$ along the inclusion of $U_a$ to the unit module $\mathcal O_{U_a}$, one for each $a : \iota$. For a strictly increasing $s : \mathrm{Fin}(i+1) \to \iota$ write $\mathcal V.\mathrm{inter}\,s = \bigsqcap_j U_{s(j)}$; for $s$ of degree $1$ the section $\tau.\mathrm{transition}\,s \in \Gamma(Y, \mathcal V.\mathrm{inter}\,s)$ is obtained by evaluating at $1$ the automorphism of the unit module on $\mathcal V.\mathrm{inter}\,s$ got by composing the inverse of the restricted $\tau_{s(0)}$ with the restricted $\tau_{s(1)}$. The assertion is twofold: firstly, $\tau.\mathrm{transition}\,s$ is a unit in $\Gamma(Y, \mathcal V.\mathrm{inter}\,s)$ for every strictly increasing pair $s$; secondly, for every strictly increasing triple $r$ the restrictions to $\mathcal V.\mathrm{inter}\,r$ of the transition sections of the faces of $r$ satisfy $u_{\mathrm{face}(r,2)} \cdot u_{\mathrm{face}(r,0)} = u_{\mathrm{face}(r,1)}$, the restriction maps being those of the structure presheaf along the inclusions $\mathcal V.\mathrm{inter}\,r \le \mathcal V.\mathrm{inter}(\mathcal V.\mathrm{face}\,r\,j)$.
--
--   This is the standard fact that the transition functions of a trivialised module on a cover are invertible and form a Čech $1$-cocycle, here for the ordered covers used in the Čech description of the Picard group. It serves the lemmas producing Picard obstruction and deformation cocycles from a Čech trivialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_isUnit_transition_and_transition_face_mul_eq.lean

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

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.isUnit_transition_and_transition_face_mul_eq
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover) (𝓜 : Y.Modules)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    (∀ s : 𝒱.Idx 1, IsUnit (τ.transition s)) ∧
    ∀ r : 𝒱.Idx 2,
      (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 2)).op).hom (τ.transition (𝒱.face r 2)) *
          (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 0)).op).hom (τ.transition (𝒱.face r 0)) =
        (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 1)).op).hom (τ.transition (𝒱.face r 1)) := by sorry
