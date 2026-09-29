-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app
-- name    : AlgebraicGeometry.Scheme.Modules.shortExact_map_pushforward_of_forall_exists_surjective_app
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/a9fa5b89-1859-5d12-a788-846e107f59ae
-- title:
--   Pushforward of a short exact sequence with locally surjective sections
-- statement:
--   Let $\pi\colon X\to T$ be a morphism of schemes and let $S$ be a short complex $S_1\xrightarrow{f}S_2\xrightarrow{g}S_3$ in the category `X.Modules` of sheaves of $\mathcal O_X$-modules. Assume $S$ is short exact, i.e. $f$ is a monomorphism and the complex is exact. Assume further that for every open $U\subseteq T$ and every point $y\in U$ there is an open $V\subseteq T$ with $y\in V$, $V\le U$, such that the map on sections $S.g$ over the preimage open $\pi^{-1}V$, that is $\Gamma(\pi^{-1}V,S_2)\to\Gamma(\pi^{-1}V,S_3)$, is surjective as a function. Then the short complex obtained from $S$ by applying the pushforward functor `Scheme.Modules.pushforward π` termwise, whose sections over an open $U\subseteq T$ are the sections of the corresponding term of $S$ over $\pi^{-1}U$, is again short exact: the pushed-forward $f$ is a monomorphism and the pushed-forward complex of $\mathcal O_T$-modules is exact. Note that surjectivity is required only over preimages of arbitrarily small opens, not over all preimages.
--
--   This is the sectionwise criterion for the direct image functor $\pi_*$ to preserve a short exact sequence of module sheaves, the concrete substitute for the vanishing of $R^1\pi_*$ on the kernel term. It is used in the construction of relative Picard data, for instance by [`AlgebraicGeometry.RelPicard.shortExact_map_pushforward_thickening`](thm.html#AlgebraicGeometry.RelPicard.shortExact_map_pushforward_thickening) and in the analysis of pushforwards of twists along a family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.shortExact_map_pushforward_of_forall_exists_surjective_app
    {X T : Scheme.{u}} (π : X ⟶ T) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hsurj : ∀ (U : T.Opens), ∀ y ∈ U, ∃ V : T.Opens, y ∈ V ∧ V ≤ U ∧
      Function.Surjective (S.g.app (π ⁻¹ᵁ V))) :
    (S.map (Scheme.Modules.pushforward π)).ShortExact := by sorry
