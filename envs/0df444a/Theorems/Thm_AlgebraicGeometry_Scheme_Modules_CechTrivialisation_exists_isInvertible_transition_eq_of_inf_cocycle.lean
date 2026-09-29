-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle
-- name    : AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_isInvertible_transition_eq_of_inf_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/47b399e8-1de8-550f-a606-29eddd8a19ed
-- title:
--   Invertible module from a unit Čech 1-cocycle
-- statement:
--   Let $Y$ be a scheme and let $\mathcal{V}$ be an ordered affine cover of $Y$, that is, a finite linearly ordered index type $\mathcal{V}.\iota$ together with opens $\mathcal{V}.U\,i$, each affine, whose supremum is $\top$. Let $W$ assign to every ordered pair $a,b$ of indices (including $a=b$) a section $W_{ab}\in\Gamma(Y,\mathcal{V}.U\,a\sqcap\mathcal{V}.U\,b)$, and assume: $W_{aa}=1$ for all $a$; each $W_{ab}$ is a unit in its ring of sections; and the cocycle identity holds for all $a,b,c$, namely the restrictions of $W_{ab}$ and $W_{bc}$ to $\mathcal{V}.U\,a\sqcap\mathcal{V}.U\,b\sqcap\mathcal{V}.U\,c$ have product equal to the restriction of $W_{ac}$ there. Then there exists a module $\mathcal{L}$ on $Y$ which is invertible in the sense of `Scheme.Modules.IsInvertible` (every point of $Y$ has an open neighbourhood $U$ for which the pullback of $\mathcal{L}$ along $U\hookrightarrow Y$ is isomorphic to the unit sheaf of modules on $U$), together with a Čech trivialisation $\tau$ of $\mathcal{L}$ on $\mathcal{V}$, i.e. isomorphisms from the pullback of $\mathcal{L}$ to $\mathcal{V}.U\,a$ onto the unit sheaf of modules on $\mathcal{V}.U\,a$ for every index $a$, whose transition sections realise $W$: for every strictly increasing $s:\mathrm{Fin}\,2\to\mathcal{V}.\iota$, the section $\tau.\mathrm{transition}\,s\in\Gamma(Y,\mathcal{V}.\mathrm{inter}\,s)$, obtained by applying `unitAutSection` to the composite of the inverse of the restricted trivialisation at $s_0$ with the restricted trivialisation at $s_1$, equals the restriction of $W_{s_0s_1}$ along $\mathcal{V}.\mathrm{inter}\,s\le \mathcal{V}.U\,s_0\sqcap\mathcal{V}.U\,s_1$.
--
--   This is Zariski descent for invertible modules in Čech form: a symmetric family of unit sections satisfying the triple-intersection cocycle identity is the family of transition sections of an invertible module trivialised on the given ordered affine cover. It is used by [`AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_isInvertible_transition_eq`](thm.html#AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_isInvertible_transition_eq), in the Čech description of invertible modules underlying the treatment of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_isInvertible_transition_eq_of_inf_cocycle
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover)
    (W : ∀ a b : 𝒱.ι, Γ(Y, 𝒱.U a ⊓ 𝒱.U b))
    (hW1 : ∀ a : 𝒱.ι, W a a = 1) (hWu : ∀ a b : 𝒱.ι, IsUnit (W a b))
    (hWc : ∀ a b c : 𝒱.ι,
      (Y.presheaf.map (homOfLE (inf_le_left : 𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U b)).op).hom (W a b) *
          (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U b ⊓ 𝒱.U c)).op).hom (W b c) =
        (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U c)).op).hom (W a c)) :
    ∃ 𝓛 : Y.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      ∃ τ : Scheme.Modules.CechTrivialisation 𝒱 𝓛, ∀ s : 𝒱.Idx 1,
        τ.transition s =
          (Y.presheaf.map (homOfLE (le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1) :
            𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1))).op).hom (W (s.1 0) (s.1 1)) := by sorry
