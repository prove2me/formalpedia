-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/94a6ce30-cdbe-56f7-88a8-4840037d8263
-- title:
--   Rank-n local freeness of π_*F from fibrewise Čech data
-- statement:
--   Let $A$ be a Noetherian commutative ring, $X$ a scheme and $\pi\colon X\to\operatorname{Spec}A$ a flat morphism. Let $\mathcal V$ be a two-chart affine open cover of $X$, that is, opens $U_0,U_1$ with $U_0$, $U_1$ and $U_0\cap U_1$ affine and $U_0\cup U_1=X$, and let $F$ be a sheaf of modules on $X$. Assume: (i) every point of $X$ has an open neighbourhood $V$ such that the pullback of $F$ along the inclusion $V\hookrightarrow X$ is isomorphic to the unit sheaf of modules on $V$ (the structure sheaf of $V$ viewed as a module over itself); (ii) writing $d=(-r_0)\oplus r_1\colon \Gamma(F,U_0)\times\Gamma(F,U_1)\to\Gamma(F,U_0\cap U_1)$ for the difference of the two restrictions, regarded as $A$-linear via $\pi$, both $\ker d$ and $\operatorname{coker} d$ are finite $A$-modules. Let $n$ be a natural number and assume: (iii) for every field $K$ carrying an $A$-algebra structure, forming the fibre product $X\times_{\operatorname{Spec}A}\operatorname{Spec}K$ with the cover obtained by taking preimages of $U_0,U_1$ under the first projection, the structure morphism the second projection, and the module the pullback of $F$ along the first projection, the corresponding $\operatorname{coker} d$ is a subsingleton and the corresponding $\ker d$ has $K$-dimension $n$. Then $(\pi_*F)$ is locally free of rank $n$: every point of $\operatorname{Spec}A$ has an open neighbourhood $U$ on which the pullback of $(\pi_*F)$ along $U\hookrightarrow\operatorname{Spec}A$ is isomorphic to the free sheaf of modules on an $n$-element index type.
--
--   This is the degree-zero case of cohomology and base change, in two-chart Čech form: fibrewise vanishing of $H^1$ together with constant fibre dimension $h^0=n$ forces the direct image to be locally free of rank $n$. It is used in the construction of the relative Picard functor, where it supplies local freeness of pushforwards of invertible modules along flat families with a two-chart affine cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A)) [Flat π]
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1) (n : ℕ)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1 ∧
      Module.finrank K ((𝒱.pullback π K).sectionsOf (pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward π).obj F) := by sorry
