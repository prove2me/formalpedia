-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_trivSqZeroExt_map_apply
-- name    : AlgebraicGeometry.SmallExtension.tangentCoords_comp_map_trivSqZeroExt_map_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/a1cefd28-13c7-5e37-ada9-9f1da55ef9ae
-- title:
--   Tangent coordinates twisted by κ[φ_V] precompose the dual vector
-- statement:
--   Let $T'$ be a commutative local ring with residue field $\kappa =$ `ResidueField T'`, let $V$ be an abelian group carrying commuting left and right $\kappa$-module structures that agree (a central scalar action), let $C$ be a commutative $T'$-algebra, and write $E = (\kappa \otimes_{T'} C) \otimes_{\kappa} \mathrm{TrivSqZeroExt}\,\kappa\,V$ for the thickening `thickening T' V C`. Let $\varphi_V \colon V \to V$ be $\kappa$-linear, let $A$ be a commutative ring, $\chi \colon A \to E$ a ring homomorphism, $a \in A$ and $\xi$ a $\kappa$-linear functional on $V$. Recall that `tangentCoords T' V C χ a` is the $\kappa$-linear map $V^{\vee} \to \kappa \otimes_{T'} C$ obtained by applying to $\chi(a)$ the map $\mathrm{id} \otimes \mathrm{snd}$ (the $V$-part, `vPart`) and then `tensorToDualHom`, which sends $m \otimes w$ to $\xi \mapsto \xi(w)\cdot m$. The assertion is that for the ring homomorphism obtained by composing $\chi$ with the underlying ring map of the algebra map $\mathrm{id}_{\kappa \otimes_{T'} C} \otimes \mathrm{TrivSqZeroExt.map}\,\varphi_V$ on $E$, the tangent coordinate at $a$ evaluated at $\xi$ equals `tangentCoords T' V C χ a` evaluated at $\xi \circ \varphi_V$.
--
--   This is the functoriality of tangent coordinates on a thickened reduction under a twist of the square-zero part: twisting by $\kappa[\varphi_V]$ on the source is the same as precomposing the dual argument with $\varphi_V$, i.e. the transpose action on $V^{\vee}$. It is used in the assembly of tangent-coordinate data for bare deformations, in [`GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_of_comp_eq_of_over_over_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_of_comp_eq_of_over_over_bare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_trivSqZeroExt_map_apply.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct IsLocalRing AlgebraicGeometry AlgebraicGeometry.SmallExtension

universe u

theorem AlgebraicGeometry.SmallExtension.tangentCoords_comp_map_trivSqZeroExt_map_apply
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]
    (φV : V →ₗ[ResidueField T'] V)
    {A : Type u} [CommRing A] (χ : A →+* thickening T' V C) (a : A) (ξ : Module.Dual (ResidueField T') V) :
    tangentCoords T' V C
        ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
          (TrivSqZeroExt.map (R' := ResidueField T') φV)).toRingHom.comp χ) a ξ =
      tangentCoords T' V C χ a (ξ ∘ₗ φV) := by sorry
