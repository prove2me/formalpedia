-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_locallyTrivial_opensRange_nonempty_pullback_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/338a9f02-0ddf-5d14-ad09-b96f8fabd0dd
-- title:
--   Extending an invertible module along an open immersion
-- statement:
--   Let $j \colon U \to X$ be a morphism of schemes (in a fixed universe) which is an open immersion, and let $M$ be an object of `U.Modules`, i.e. a sheaf of modules over the sheaf of rings of $U$. Assume `Scheme.Modules.IsInvertible M`, which by definition says that for every point $x$ of $U$ there is an open $V \subseteq U$ containing $x$ such that the pullback of $M$ along the inclusion $V.\iota$ admits an isomorphism to the unit module $\mathcal{O}_V$ on $V$. The assertion is that there exists an object $\mathcal{L}$ of `X.Modules` with two properties. First, $\mathcal{L}$ is trivial near every point of the open image of $j$, in the following inline sense: for each $x$ in `Scheme.Hom.opensRange j` there is an open $U' \subseteq X$ with $x \in U'$, with $U'$ contained in the open range of $j$, and such that the pullback of $\mathcal{L}$ along $U'.\iota$ is isomorphic to the unit module on $U'$. Second, the pullback of $\mathcal{L}$ along $j$ is isomorphic to $M$. Both isomorphism clauses are stated as non-emptiness of the type of isomorphisms. Nothing is asserted about $\mathcal{L}$ outside the image of $j$; in particular $\mathcal{L}$ is not claimed to be invertible on all of $X$.
--
--   This is the extension step for invertible modules along an open immersion: an invertible sheaf on an open subscheme is the restriction of a module on the ambient scheme which is locally trivial over that open subscheme. It is used in the proof that restriction of line bundles to an open subscheme is surjective up to isomorphism, in the form [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk), which feeds the construction of rigidified line bundles used for relative Picard functors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_locallyTrivial_opensRange_nonempty_pullback_iso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : U.Modules} (hM : Scheme.Modules.IsInvertible M) :
    ∃ 𝓛 : X.Modules,
      (∀ x ∈ Scheme.Hom.opensRange j, ∃ U : X.Opens, x ∈ U ∧ U ≤ Scheme.Hom.opensRange j ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)) ∧
      Nonempty ((Scheme.Modules.pullback j).obj 𝓛 ≅ M) := by sorry
