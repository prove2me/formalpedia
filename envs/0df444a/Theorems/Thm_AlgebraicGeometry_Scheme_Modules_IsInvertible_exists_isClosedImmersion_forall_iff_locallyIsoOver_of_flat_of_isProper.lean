-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/f3c6de1d-2c74-5b43-9905-e372c89822b6
-- title:
--   See-saw theorem over a general base ring
-- statement:
--   Let $R$ be a commutative ring and let $c : X \to \operatorname{Spec} R$ be a morphism of schemes that is proper, flat and satisfies the predicate `GeometricallyIntegral`. Assume further that for every commutative $R$-algebra $B$ the map on global sections induced by the projection $X \times_{\operatorname{Spec} R} \operatorname{Spec} B \to \operatorname{Spec} B$ is bijective, i.e. $B \xrightarrow{\ \sim\ } \Gamma(X_B, \mathcal O)$ universally. Let $T$ be a locally Noetherian scheme with a morphism $t : T \to \operatorname{Spec} R$, and let $M, M'$ be modules on the fibre product $X \times_{\operatorname{Spec} R} T$, each invertible in the sense that every point has an open neighbourhood $U$ over which the restriction of the module is isomorphic to the unit module on $U$. The conclusion asserts the existence of a scheme $Z$ and a closed immersion $\iota : Z \to T$ with the following universal property: for every scheme $T'$ and every morphism $\psi : T' \to T$, there is a morphism $z : T' \to Z$ with $z$ followed by $\iota$ equal to $\psi$ if and only if the pull-backs of $M$ and $M'$ along the projection $(X \times_{\operatorname{Spec} R} T) \times_T T' \to X \times_{\operatorname{Spec} R} T$ are locally isomorphic over $T'$, meaning that every point of $T'$ has an open neighbourhood $U$ such that the two pull-backs become isomorphic after restriction to the preimage of $U$ under the projection to $T'$.
--
--   This is Mumford's see-saw principle in scheme-theoretic form, formulated over an arbitrary base ring rather than a field: the locus in $T$ over which two invertible modules on a proper flat family with geometrically integral fibres agree up to a line bundle pulled back from the base is representable by a closed subscheme of $T$. It is used to produce charts for the relative Picard functor of such a family, and to construct the stabiliser subscheme $K(\mathcal L)$ attached to a line bundle on an abelian scheme (taking $X = T$ the abelian scheme, $M$ the pull-back of $\mathcal L$ along the group law and $M'$ its pull-back along a projection).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] [GeometricallyIntegral c]
    (hH0 : ∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective (Limits.pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
    {T : Scheme.{u}} [IsLocallyNoetherian T] (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : (Limits.pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hM' : Scheme.Modules.IsInvertible M') :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ T), IsClosedImmersion ι ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T),
        (∃ z : T' ⟶ Z, z ≫ ι = ψ) ↔
          Scheme.Modules.LocallyIsoOver (Limits.pullback.snd (Limits.pullback.snd c t) ψ)
            ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) ψ)).obj M)
            ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) ψ)).obj M') := by sorry
