-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_locallyIso_of_locallyIso_pullback_pi_localizationAway
-- name    : AlgebraicGeometry.Scheme.Modules.locallyIso_of_locallyIso_pullback_pi_localizationAway
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/c31a72da-e612-5c92-a75a-0ad244721af5
-- title:
--   Local isomorphy descends along a finite principal cover
-- statement:
--   Let $S$ be a commutative ring, $k$ a natural number and $r : \mathrm{Fin}\,k \to S$ a family whose range generates the unit ideal of $S$, and put $S_1 := \prod_{i} S[1/r_i]$, where $S[1/r_i]$ is the localisation of $S$ away from $r_i$. Let $f : X \to \operatorname{Spec} S$ and $f_1 : X_1 \to \operatorname{Spec} S_1$ be morphisms of schemes and $c : X_1 \to X$ a morphism such that the square formed by $c$, $f_1$, $f$ and $\operatorname{Spec}$ of the structure map $S \to S_1$ is cartesian (with $c$, $f_1$ the projections). Let $L$ and $M$ be objects of `X.Modules`. Assume that for every point $s_1$ of $\operatorname{Spec} S_1$ there is an open $U_1 \subseteq \operatorname{Spec} S_1$ containing $s_1$ for which the restrictions along the inclusion of the open subscheme $f_1^{-1}U_1 \subseteq X_1$ of the pullbacks $c^{*}L$ and $c^{*}M$ are isomorphic (an isomorphism exists, the type being asserted nonempty). Then for every point $s$ of $\operatorname{Spec} S$ there is an open $U \subseteq \operatorname{Spec} S$ containing $s$ such that the restrictions of $L$ and $M$ along the inclusion of $f^{-1}U \subseteq X$ are isomorphic.
--
--   This is the Zariski descent step for the property 'isomorphic locally on the base', for the finite cover of $\operatorname{Spec} S$ by the basic opens $D(r_i)$ packaged as the single affine morphism $\operatorname{Spec}\prod_i S[1/r_i] \to \operatorname{Spec} S$. It is used in the comparison of polarised abelian schemes, where the analogous statement for local isomorphy of module sheaves after base change to a product of localisations is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_locallyIso_of_locallyIso_pullback_pi_localizationAway.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.locallyIso_of_locallyIso_pullback_pi_localizationAway
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    {X X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (f₁ : X₁ ⟶ Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i))))
    (c : X₁ ⟶ X) (hc : IsPullback c f₁ f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i))))))
    (L M : X.Modules)
    (h : ∀ s₁ : ↥(Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))),
      ∃ U₁ : (Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))).Opens, s₁ ∈ U₁ ∧
        Nonempty ((Scheme.Modules.pullback (f₁ ⁻¹ᵁ U₁).ι).obj ((Scheme.Modules.pullback c).obj L) ≅
          (Scheme.Modules.pullback (f₁ ⁻¹ᵁ U₁).ι).obj ((Scheme.Modules.pullback c).obj M))) :
    ∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M) := by sorry
