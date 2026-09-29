-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one
-- name    : AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/cb9348ef-3751-5f43-b4cc-896144664a42
-- title:
--   Gluing a Čech trivialisation with trivial transitions, charts preserved
-- statement:
--   Let $Y$ be a scheme and let $\mathcal V$ be an ordered affine cover of $Y$: a finite, linearly ordered index type $\mathcal V.\iota$ together with opens $\mathcal V.U\,a$, each affine, whose supremum is $\top$. Let $\mathcal M$ be an $\mathcal O_Y$-module, and let $\tau$ be a Čech trivialisation of $\mathcal M$ relative to $\mathcal V$, i.e. for each index $a$ an isomorphism $\tau\,a$ from the pullback of $\mathcal M$ along the inclusion $(\mathcal V.U\,a).\iota$ to the unit module on the open subscheme $\mathcal V.U\,a$. Assume that for every $s$ in $\mathcal V.\mathrm{Idx}\,1$, that is every strictly increasing pair $s : \mathrm{Fin}\,2 \to \mathcal V.\iota$, the transition section $\tau.\mathrm{transition}\,s \in \Gamma(Y, \mathcal V.\mathrm{inter}\,s)$ equals $1$; here $\mathcal V.\mathrm{inter}\,s = \mathcal V.U(s\,0) \sqcap \mathcal V.U(s\,1)$ and the transition is $\mathrm{unitAutSection}$ of the automorphism of the unit module on that intersection obtained by composing the inverse of $\tau$ restricted from the chart $s\,0$ with $\tau$ restricted from the chart $s\,1$, $\mathrm{unitAutSection}\,W\,e$ being the value of $e$ on the section $1$, transported along the isomorphism $\Gamma(W, \top) \cong \Gamma(Y, W)$. The conclusion asserts the existence of a global isomorphism $\varphi : \mathcal M \cong \mathcal O_Y$ (the unit module of $Y$) such that for every index $a$ the section $\mathrm{unitAutSection}(\mathcal V.U\,a)$ of the composite of $(\tau\,a)^{-1}$, the pullback of $\varphi$ along $(\mathcal V.U\,a).\iota$, and the canonical identification of the pullback of the unit module with the unit module on $\mathcal V.U\,a$, equals $1$ in $\Gamma(Y, \mathcal V.U\,a)$; that is, $\varphi$ restricts on each chart to the given $\tau\,a$.
--
--   This is the gluing step for line bundles in Čech form, strengthened so that the glued global trivialisation induces exactly the prescribed charts rather than merely some trivialisation: vanishing of all Čech transitions forces $\mathcal M$ to be isomorphic to $\mathcal O_Y$ compatibly with $\tau$. It is used in the construction of Picard deformation cocycles for small extensions, in [`AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_forall_d_eq_zero`](thm.html#AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_forall_d_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one
    {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    (h : ∀ s : 𝒱.Idx 1, τ.transition s = 1) :
    ∃ φ : 𝓜 ≅ SheafOfModules.unit Y.ringCatSheaf, ∀ a : 𝒱.ι,
      Scheme.Modules.unitAutSection (𝒱.U a)
        ((τ a).symm ≪≫ (Scheme.Modules.pullback (𝒱.U a).ι).mapIso φ ≪≫
          Scheme.Modules.pullbackUnitIso (𝒱.U a).ι) = 1 := by sorry
