-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_add_eq_add
-- name    : AlgebraicGeometry.SmallExtension.tangentCoords_comp_map_add_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/d05f3c23-ac0a-5cd6-8807-b5b14cc01cc0
-- title:
--   Additivity of tangent coordinates along the sum map
-- statement:
--   Fix a local ring $T'$ with residue field $k = \mathrm{ResidueField}\,T'$, a $k$-vector space $V$ (carrying compatible left and right $k$-actions, the right one central), and a commutative $T'$-algebra $C$; write $C_k = k \otimes_{T'} C$. For a $k$-space $W$ put $\mathrm{thickening}\,T'\,W\,C = C_k \otimes_k (k \oplus W)$, where $k \oplus W$ is the trivial square-zero extension `TrivSqZeroExt`. For a commutative ring $A$ and a ring homomorphism $\varphi \colon A \to \mathrm{thickening}\,T'\,W\,C$, the tangent coordinates of $\varphi$ send $a \in A$ to the element of $\mathrm{Hom}_k(W^\vee, C_k)$ obtained from $\mathrm{vPart}(\varphi(a)) = (\mathrm{id}_{C_k} \otimes \mathrm{snd})(\varphi(a)) \in C_k \otimes_k W$ by the canonical map sending $c \otimes w$ to $\xi \mapsto \xi(w)\,c$. Each $k$-linear map $h \colon V \times V \to V$ induces $\mathrm{id}_{C_k} \otimes (k \oplus h) \colon \mathrm{thickening}\,T'\,(V \times V)\,C \to \mathrm{thickening}\,T'\,V\,C$. The assertion is that for every commutative ring $A$ and every ring homomorphism $\psi \colon A \to \mathrm{thickening}\,T'\,(V \times V)\,C$, the tangent coordinates of the composite of $\psi$ with the map induced by $\mathrm{pr}_1 + \mathrm{pr}_2$ equal, as functions on $A$ with values in $\mathrm{Hom}_k(V^\vee, C_k)$, the sum of the tangent coordinates of the composites of $\psi$ with the maps induced by $\mathrm{pr}_1$ and by $\mathrm{pr}_2$.
--
--   This is the coordinate form of the statement that addition of tangent vectors to a square-zero thickening is computed through the two projections $k \oplus (V \times V) \to k \oplus V$: restricting a map into the double thickening along the sum of the projections adds the tangent coordinates. It is used by [`AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_add`](thm.html#AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_add) and [`AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add`](thm.html#AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_add_eq_add.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

theorem AlgebraicGeometry.SmallExtension.tangentCoords_comp_map_add_eq_add
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]
    {A : Type u} [CommRing A] (ψ : A →+* thickening T' (V × V) C) :
    tangentCoords T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
        (TrivSqZeroExt.map (LinearMap.fst (ResidueField T') V V + LinearMap.snd (ResidueField T') V V))).toRingHom.comp ψ) =
      tangentCoords T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
        (TrivSqZeroExt.map (LinearMap.fst (ResidueField T') V V))).toRingHom.comp ψ) +
      tangentCoords T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
        (TrivSqZeroExt.map (LinearMap.snd (ResidueField T') V V))).toRingHom.comp ψ) := by sorry
