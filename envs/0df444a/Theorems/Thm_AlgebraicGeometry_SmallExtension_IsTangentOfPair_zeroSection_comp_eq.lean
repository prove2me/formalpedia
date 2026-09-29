-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_IsTangentOfPair_zeroSection_comp_eq
-- name    : AlgebraicGeometry.SmallExtension.IsTangentOfPair.zeroSection_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/c4ffc0c5-f91a-5bfb-b5e2-840cc0965105
-- title:
--   Zero section of a tangent field of a pair recovers u
-- statement:
--   Let $T'$ be a commutative local ring with residue field $k = \operatorname{ResidueField} T'$, let $I \subseteq T'$ be an ideal, and let $V$ be an abelian group carrying compatible left and right $k$-module structures with the same underlying action, together with a $T'$-module structure for which the scalars factor through $k$. Let $\iota \colon V \to T'$ be a $T'$-linear map whose range, viewed as a $T'$-submodule, is $I$, and let $C$ be a commutative $T'$-algebra. Write $C_k = k \otimes_{T'} C$ and let $E = C_k \otimes_k (k \oplus V)$ be the `thickening`, where $k \oplus V$ is the trivial square-zero extension. Let $Y$ be a scheme and let $u, v \colon \operatorname{Spec} C \to Y$ and $w \colon \operatorname{Spec} E \to Y$ be morphisms such that `IsTangentOfPair I V ι C u v w` holds, i.e. there are a ring homomorphism $\vartheta$ from the fibre product $\{(a,b) \in C \times C : a \equiv b \bmod I C\}$ (the `pairRing`) to $E$ with $\vartheta(a,a) = (1 \otimes a) \otimes 1$ for all $a$ and $\vartheta(0, \iota(x) c) = (1 \otimes c) \otimes \operatorname{inr} x$ for all $x \in V$, $c \in C$, and a morphism $\varphi \colon \operatorname{Spec}(\mathrm{pairRing}) \to Y$ with $\operatorname{Spec}(\mathrm{pairFst})$ followed by $\varphi$ equal to $u$, $\operatorname{Spec}(\mathrm{pairSnd})$ followed by $\varphi$ equal to $v$, and $w = \operatorname{Spec}(\vartheta)$ followed by $\varphi$. Then the zero section $\operatorname{Spec} C_k \to \operatorname{Spec} E$ — the morphism into the cartesian square `thickening_isPullback` with components the identity of $\operatorname{Spec} C_k$ and the base point of $\operatorname{Spec}(k \oplus V)$ precomposed with $\operatorname{Spec} C_k \to \operatorname{Spec} k$ — followed by $w$ equals $\operatorname{Spec}$ of the structural map $C \to k \otimes_{T'} C$, $c \mapsto 1 \otimes c$, followed by $u$.
--
--   This records that the tangent field $w$ attached to a pair $(u,v)$ of $C$-points agreeing modulo $IC$ restricts along the zero section of the square-zero thickening to the reduction of the first point $u$, the usual normalisation in Schlessinger-style deformation theory. It is used in the two uniqueness statements [`AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia`](thm.html#AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia) and [`AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAt_of_isTangentCoordsOfPairAt`](thm.html#AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAt_of_isTangentCoordsOfPairAt), whose hypotheses are phrased in exactly this shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_IsTangentOfPair_zeroSection_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

theorem AlgebraicGeometry.SmallExtension.IsTangentOfPair.zeroSection_comp_eq
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y) (w : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y)
    (huvw : IsTangentOfPair I V ι C u v w) :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) ≫ w
      = Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ u := by sorry
