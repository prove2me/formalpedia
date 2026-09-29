-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_faithfullyFlat_of_isLocalRing
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_faithfullyFlat_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/7f6bca1e-c8c0-5a00-97f8-f74d86ea91b4
-- title:
--   Descent of isomorphisms of invertible modules along faithfully flat base change
-- statement:
--   Let $S$ be a local commutative ring and $S'$ a commutative $S$-algebra which is faithfully flat as an $S$-module. Let $A,A'$ be schemes, $f\colon A\to\operatorname{Spec} S$ a quasi-compact separated morphism, $f'\colon A'\to\operatorname{Spec} S'$ and $g\colon A'\to A$ morphisms, and assume the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S\to S'$ is cartesian. Assume further that for every $S$-algebra $T$ the structure map $T\to\Gamma(A\times_{\operatorname{Spec} S}\operatorname{Spec} T,\mathcal O)$ is bijective, where the $T$-algebra structure on the global sections is the one induced by the second projection to $\operatorname{Spec} T$. Finally let $\mathcal L,\mathcal L'$ be $\mathcal O_A$-modules, each satisfying `Scheme.Modules.IsInvertible`, i.e. every point of $A$ has an open neighbourhood $U$ such that the restriction of the module along the inclusion $U\hookrightarrow A$ is isomorphic to the unit module $\mathcal O_U$, and suppose there exists an isomorphism $g^*\mathcal L\cong g^*\mathcal L'$. Then there exists an isomorphism $\mathcal L\cong\mathcal L'$ (the conclusion asserts only non-emptiness of the set of isomorphisms, with no compatibility with the given one).
--
--   This is the injectivity, over a local base with universally trivial $H^0$, of the base-change map on isomorphism classes of line bundles: faithfully flat descent for the relative Picard group. It is used in the Čerednik–Drinfeld part of the development, in the proofs that a canonical polarisation on a fake elliptic curve induces an isomorphism on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_faithfullyFlat_of_isLocalRing.lean

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_faithfullyFlat_of_isLocalRing
    {S : Type u} [CommRing S] [IsLocalRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hiso : Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ (Scheme.Modules.pullback g).obj 𝓛')) :
    Nonempty (𝓛 ≅ 𝓛') := by sorry
