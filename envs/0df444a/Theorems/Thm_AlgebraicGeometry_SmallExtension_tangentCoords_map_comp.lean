-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_tangentCoords_map_comp
-- name    : AlgebraicGeometry.SmallExtension.tangentCoords_map_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/18e5105e-09c3-5d23-a407-e2f608de8d89
-- title:
--   Naturality of `tangentCoords` in the chart algebra
-- statement:
--   Let $T'$ be a commutative local ring with residue field $k =$ `ResidueField T'`, and let $V$ be an abelian group carrying compatible left and right $k$-module structures with centrally acting scalars (so that the trivial square-zero extension `TrivSqZeroExt k V` is a $k$-algebra). Let $C$ and $C'$ be commutative $T'$-algebras and $h \colon C \to C'$ a $T'$-algebra homomorphism. For an algebra $D$ write $E_D = (k \otimes_{T'} D) \otimes_k \mathrm{TrivSqZeroExt}(k,V)$ for the thickening `thickening T' V D`, and let $E_h = (\mathrm{id}_k \otimes h) \otimes \mathrm{id} \colon E_C \to E_{C'}$ be the induced $k$-algebra homomorphism. Let $A$ be a commutative ring, $\varphi \colon A \to E_C$ a ring homomorphism and $a \in A$. Recall that `tangentCoords T' V C φ a` is the $k$-linear map $V^\vee \to k \otimes_{T'} C$ obtained by applying `tensorToDualHom`, which sends a pure tensor $m \otimes w$ to $\xi \mapsto \xi(w)\, m$, to the image of $\varphi(a)$ under `vPart`, namely under $\mathrm{id} \otimes \mathrm{snd} \colon E_C \to (k \otimes_{T'} C) \otimes_k V$. The assertion is that the tangent coordinates for $C'$ of the ring homomorphism $E_h \circ \varphi$ at $a$ coincide with the composite of `tangentCoords T' V C φ a` followed by the $k$-linear map underlying $\mathrm{id}_k \otimes h$.
--
--   This records that the canonical tangent coordinates attached to a point of a thickening are natural in the chart algebra: changing $C$ along a $T'$-algebra map $h$ post-composes the coordinates with $\mathrm{id}_k \otimes h$. It is used in [`AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat`](thm.html#AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat) and [`AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat`](thm.html#AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat), where tangent coordinates of a pair must be compared under flat change of chart, for instance on affine overlaps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_tangentCoords_map_comp.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

theorem AlgebraicGeometry.SmallExtension.tangentCoords_map_comp
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C] (C' : Type u) [CommRing C'] [Algebra T' C'] (h : C →ₐ[T'] C')
    {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a : A) :
    tangentCoords T' V C'
        ((Algebra.TensorProduct.map
            (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h)
            (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V)) :
          thickening T' V C →ₐ[ResidueField T'] thickening T' V C').toRingHom.comp φ) a =
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h).toLinearMap ∘ₗ tangentCoords T' V C φ a := by sorry
