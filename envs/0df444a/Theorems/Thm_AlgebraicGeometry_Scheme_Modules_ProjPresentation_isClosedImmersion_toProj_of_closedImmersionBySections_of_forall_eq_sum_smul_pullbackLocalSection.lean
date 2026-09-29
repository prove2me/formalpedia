-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_closedImmersionBySections_of_forall_eq_sum_smul_pullbackLocalSection
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_closedImmersionBySections_of_forall_eq_sum_smul_pullbackLocalSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/bddcb5d0-d835-5353-b4fc-9a39d87b7a4b
-- title:
--   Closed immersion from a presentation by spanning pulled-back sections
-- statement:
--   Let $S$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} S$ a morphism, $M$ an $\mathcal{O}_X$-module, and $\sigma_0,\dots,\sigma_N$ global sections of $M$ (sections over $\top$). Let $k$ be a field and $sk : S \to k$ a ring homomorphism, and write $g$ and $f_k$ for the two projections of the fibre product of $f$ along $\operatorname{Spec}(sk)$, so $g$ maps $X \times_{\operatorname{Spec} S} \operatorname{Spec} k$ to $X$ and $f_k$ maps it to $\operatorname{Spec} k$. Assume: (i) `ClosedImmersionBySections` holds for $g^{*}M$ relative to $f_k$, that is, for some $N'$ there is a `ProjPresentation` $\mathfrak{Q}$ of $g^{*}M$ over $f_k$ with $N'+1$ sections whose structure morphism $\mathfrak{Q}.\mathrm{toProj}$ to $\mathbb{P}^{N'}_k = \operatorname{Proj}$ of the homogeneous subalgebra of $k[X_0,\dots,X_{N'}]$ is a closed immersion; (ii) every section $t$ of $g^{*}M$ over $\top$ is a finite $k$-linear combination $\sum_i c_i \cdot \mathrm{pullbackLocalSection}\,g\,(\sigma_i)$, the $k$-action being the one obtained from $f_k$ on sections over $g^{-1}\top$; and (iii) $\mathfrak{P}'$ is a `ProjPresentation` of $g^{*}M$ over $f_k$ with $N+1$ sections, each $\mathfrak{P}'.\sigma_i$ being the image of $\sigma_i$ under the unit of the pullback–pushforward adjunction for $g$ at $\top$. Then $\mathfrak{P}'.\mathrm{toProj} : X \times_{\operatorname{Spec} S} \operatorname{Spec} k \to \mathbb{P}^{N}_k$ is a closed immersion. Recall that a `ProjPresentation` consists of such sections, a morphism to the relevant $\operatorname{Proj}$ lying over the base morphism, a framing condition stating that on opens lying over the basic open of $X_i$ multiplication by the restriction of $\sigma_i$ is bijective from functions to sections, and the compatibility of the $\sigma_i$ with the coordinate ratios pulled back from $\operatorname{Proj}$.
--
--   This is the standard criterion that a system of sections which spans the sections belonging to an already-known projective embedding again defines a closed immersion, transplanted to a geometric fibre $X \times_S \operatorname{Spec} k$ of $f$ and to the project's notion of a presentation of a module by sections. It feeds the verification that a family of sections yields a closed immersion fibrewise, used in the construction of good models of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_closedImmersionBySections_of_forall_eq_sum_smul_pullbackLocalSection.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_closedImmersionBySections_of_forall_eq_sum_smul_pullbackLocalSection
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules)
    {N : ℕ} (σ : Fin (N + 1) → Γ(M, ⊤))
    (k : Type u) [Field k] (sk : S →+* k)
    (hfib : Scheme.Modules.ClosedImmersionBySections
      ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M) (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))))
    (hspan : ∀ t : Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤),
      letI : Module k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) ⁻¹ᵁ ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) ⁻¹ᵁ ⊤) le_top).hom
      ∃ c : Fin (N + 1) → k, t = ∑ i, c i • Scheme.Modules.pullbackLocalSection (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) (σ i))
    (𝔓' : Scheme.Modules.ProjPresentation ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M) (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))) N)
    (h𝔓' : ∀ i, 𝔓'.σ i =
      (((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).unit.app M).app ⊤) (σ i)) :
    IsClosedImmersion 𝔓'.toProj := by sorry
