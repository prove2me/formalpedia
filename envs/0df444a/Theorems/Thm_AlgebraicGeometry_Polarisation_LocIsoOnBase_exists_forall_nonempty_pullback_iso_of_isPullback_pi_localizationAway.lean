-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_exists_forall_nonempty_pullback_iso_of_isPullback_pi_localizationAway
-- name    : AlgebraicGeometry.Polarisation.LocIsoOnBase.exists_forall_nonempty_pullback_iso_of_isPullback_pi_localizationAway
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/19b06b71-3974-5f4a-b9ea-f3b28188884d
-- title:
--   Base-local isomorphy of modules becomes global over a product of localisations
-- statement:
--   Let $S$ be a commutative ring, $X$ a scheme, $f \colon X \to \operatorname{Spec} S$ a morphism and $M, M'$ two objects of `X.Modules`. Assume `LocIsoOnBase f M M'`, that is: for every point $s$ of $\operatorname{Spec} S$ there is an open $U \subseteq \operatorname{Spec} S$ with $s \in U$ such that the pullbacks of $M$ and of $M'$ along the inclusion $f^{-1}U \hookrightarrow X$ are isomorphic (the set of such isomorphisms is nonempty). The conclusion asserts the existence of a natural number $k$ and a family $r \colon \mathrm{Fin}\,k \to S$ whose range generates the unit ideal of $S$, such that, writing $S'' := \prod_{i < k} S[1/r_i]$ for the product of the away-localisations, for every scheme $X'$, every morphism $f' \colon X' \to \operatorname{Spec} S''$ and every morphism $c \colon X' \to X$ making the square with sides $c, f', f$ and $\operatorname{Spec}$ of the structure map $S \to S''$ cartesian, the pullbacks $c^{*}M$ and $c^{*}M'$ in `X'.Modules` are isomorphic. Only the existence of an isomorphism is claimed, with no compatibility with the base change.
--
--   This is the statement that two modules on $X$ which are isomorphic locally on the base $\operatorname{Spec} S$ become isomorphic after the base change to a finite product of principal localisations covering $\operatorname{Spec} S$ — the passage from a base-local to a global isomorphism needed when comparing polarisations. It is used in [`AlgebraicGeometry.PolarisedAbelianScheme.of_iso_of_forall_isPullback_of_forall_faithfullyFlat_etale`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.of_iso_of_forall_isPullback_of_forall_faithfullyFlat_etale).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_exists_forall_nonempty_pullback_iso_of_isPullback_pi_localizationAway.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.exists_forall_nonempty_pullback_iso_of_isPullback_pi_localizationAway
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M M' : X.Modules)
    (h : LocIsoOnBase f M M') :
    ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧
      ∀ (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))) (c : X' ⟶ X),
        IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i))))) →
        Nonempty ((Scheme.Modules.pullback c).obj M ≅ (Scheme.Modules.pullback c).obj M') := by sorry
