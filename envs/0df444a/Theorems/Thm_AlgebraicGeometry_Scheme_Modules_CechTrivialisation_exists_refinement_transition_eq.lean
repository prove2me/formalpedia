-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq
-- name    : AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_refinement_transition_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/7118bde4-d090-5331-b0b3-8c053d5ddab6
-- title:
--   Pullback of a Čech trivialisation along a refinement map
-- statement:
--   Let $h \colon X \to Y$ be a morphism of schemes, let $\mathcal V$ be an ordered affine cover of $Y$ and $\mathcal W$ one of $X$ (each given by a finite linearly ordered index type, opens $U_i$ with $U_i$ affine and $\bigsqcup_i U_i = \top$), let $\lambda \colon \mathcal W.\iota \to \mathcal V.\iota$ satisfy $\mathcal W.U\,w \le h^{-1}(\mathcal V.U\,(\lambda w))$ for all $w$, let $\mathcal M$ be an $\mathcal O_Y$-module and let $\tau$ be a Čech trivialisation of $\mathcal M$ on $\mathcal V$, i.e. a family of isomorphisms $\tau_a \colon (\mathcal V.U\,a)^*\mathcal M \cong \mathcal O_{\mathcal V.U\,a}$. Then there is a Čech trivialisation $\tau'$ of $h^*\mathcal M$ on $\mathcal W$ with the following four properties. First, for each $w$, $\tau'_w$ is the explicit composite of the pseudofunctoriality isomorphism for $(\mathcal W.U\,w).\iota$ followed by $h$, the comparison along the factorisation $(\mathcal W.U\,w).\iota \circ h = (\mathcal V.U\,(\lambda w)).\iota \circ j_w$ with $j_w := X.\mathrm{homOfLE} \circ (h \mid_{\mathcal V.U (\lambda w)})$, the inverse pseudofunctoriality isomorphism for that factorisation, the image $j_w^*\tau_{\lambda w}$, and `pullbackUnitIso` for $j_w$. Second, for a strictly monotone pair $s = (w_0 < w_1)$ in $\mathcal W.\iota$ with $\lambda w_0 = \lambda w_1$, the transition element $\tau'.\mathrm{transition}\,s \in \Gamma(X, \mathcal W.U\,w_0 \cap \mathcal W.U\,w_1)$ equals $1$. Third, if $\lambda \circ s$ is injective and $\lambda w_0 < \lambda w_1$, then $\tau'.\mathrm{transition}\,s$ is the restriction to $\mathcal W.\mathrm{inter}\,s$ of $h^\sharp$ applied to $\tau.\mathrm{transition}$ of the sorted index `sortIdx`, via the inclusion $\mathcal W.\mathrm{inter}\,s \le h^{-1}(\mathcal V.\mathrm{inter}\,(\mathrm{sortIdx}))$. Fourth, if $\lambda \circ s$ is injective and $\lambda w_1 < \lambda w_0$, then the product of $\tau'.\mathrm{transition}\,s$ with that same restricted element equals $1$.
--
--   This is the naturality statement for Čech trivialisations and their transition cocycles under an arbitrary (not necessarily affine) morphism of schemes, passing through a refinement of the inverse-image cover with an explicit index map; the sign pattern in the last two clauses records the alternation of the refined Čech cochain. It is used in the construction of Picard obstruction and deformation cocycles for small extensions, namely by [`AlgebraicGeometry.SmallExtension.exists_isPicObstructionCocycle_pullback_eq_unitPullback`](thm.html#AlgebraicGeometry.SmallExtension.exists_isPicObstructionCocycle_pullback_eq_unitPullback) and [`AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback`](thm.html#AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_refinement_transition_eq
    {X Y : Scheme.{u}} (h : X ⟶ Y) (𝒱 : Y.OrderedAffineCover) (𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝒱.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒱.U (lam w))
    (𝓜 : Y.Modules) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    ∃ τ' : Scheme.Modules.CechTrivialisation 𝒲 ((Scheme.Modules.pullback h).obj 𝓜),

      (∀ w : 𝒲.ι, τ' w =
        ((Scheme.Modules.pullbackComp (𝒲.U w).ι h).app 𝓜) ≪≫
          ((Scheme.Modules.pullbackCongr
              (show (𝒲.U w).ι ≫ h = (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w))) ≫ (𝒱.U (lam w)).ι by
                rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι])).app 𝓜) ≪≫
          ((Scheme.Modules.pullbackComp (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w))) (𝒱.U (lam w)).ι).app 𝓜).symm ≪≫
          (Scheme.Modules.pullback (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w)))).mapIso (τ (lam w)) ≪≫
          Scheme.Modules.pullbackUnitIso (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w)))) ∧

      (∀ s : 𝒲.Idx 1, lam (s.1 0) = lam (s.1 1) → τ'.transition s = 1) ∧

      (∀ (s : 𝒲.Idx 1) (hinj : Function.Injective (lam ∘ s.1)), lam (s.1 0) < lam (s.1 1) →
        τ'.transition s =
          (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj)).op).hom
            ((h.app (𝒱.inter (𝒲.sortIdx 𝒱 lam s hinj))).hom (τ.transition (𝒲.sortIdx 𝒱 lam s hinj)))) ∧

      (∀ (s : 𝒲.Idx 1) (hinj : Function.Injective (lam ∘ s.1)), lam (s.1 1) < lam (s.1 0) →
        τ'.transition s *
          (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj)).op).hom
            ((h.app (𝒱.inter (𝒲.sortIdx 𝒱 lam s hinj))).hom (τ.transition (𝒲.sortIdx 𝒱 lam s hinj))) = 1) := by sorry
