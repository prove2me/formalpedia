-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible
-- name    : AlgebraicGeometry.Scheme.Modules.exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/ac134253-dd2c-5f6a-801c-ec40520a6548
-- title:
--   Invertible module on a closed subscheme trivialises on a pulled-back ordered affine cover
-- statement:
--   Let $X$ and $X_0$ be schemes (in a fixed universe), with $X$ quasi-compact in the sense that its underlying space is a compact space, let $g \colon X_0 \to X$ be a closed immersion, and let $\mathcal L_0$ be a sheaf of modules over the structure sheaf of $X_0$ which is invertible in the sense of `Scheme.Modules.IsInvertible`: for every point $x$ of $X_0$ there is an open $U \subseteq X_0$ containing $x$ such that the pullback of $\mathcal L_0$ along the inclusion $U \hookrightarrow X_0$ is isomorphic to the unit module $\mathcal O_U$ on $U$. The assertion is that there exists an ordered affine cover $\mathcal U$ of $X$, that is, a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq X$, each affine, whose supremum is $\top$, such that the type of Čech trivialisations of $\mathcal L_0$ for the pulled-back cover $\mathcal U.\mathrm{comap}\,g$ (the cover of $X_0$ with the same index type and opens $g^{-1}U_i$) is nonempty; concretely, there is a family, indexed by $a \in \iota$, of isomorphisms between the pullback of $\mathcal L_0$ along the inclusion $g^{-1}U_a \hookrightarrow X_0$ and the unit module on $g^{-1}U_a$.
--
--   This is the local-triviality bookkeeping step which turns pointwise invertibility of a line bundle on a closed subscheme into a trivialisation along the preimage of one fixed finite ordered affine cover of the ambient scheme, the shape of data needed to set up Čech cocycles and the associated Picard obstruction. It is used in the study of line bundles on fake elliptic curves over Artinian bases, where the ambient scheme is proper over an Artinian ring (hence quasi-compact) and the special fibre embeds as a closed subscheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible
    {X X₀ : Scheme.{u}} [CompactSpace X] (g : X₀ ⟶ X) [IsClosedImmersion g]
    (𝓛₀ : X₀.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) :
    ∃ 𝒰 : X.OrderedAffineCover, Nonempty (Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓛₀) := by sorry
