-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime
-- name    : AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/aa5c1100-b4f0-595c-be21-97ea3c824412
-- title:
--   Isomorphisms of invertible modules spread out from S_𝔭 to Sᵣ
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a quasi-compact, quasi-separated morphism; let $\mathfrak p$ be a prime ideal of $S$ and $r_0 \in S$ an element with $r_0 \notin \mathfrak p$. Let $\psi : S[1/r_0] \to S_{\mathfrak p}$ be a ring homomorphism compatible with the two structure maps from $S$, i.e. $\psi \circ (S \to S[1/r_0]) = (S \to S_{\mathfrak p})$. Write $A_T$ for the fibre product of $f$ with $\operatorname{Spec} T \to \operatorname{Spec} S$. Let $\mathcal L_1, \mathcal L_2$ be modules on $A_{S[1/r_0]}$, each invertible in the sense that every point of the scheme has an open neighbourhood $U$ on which the pullback along $U \hookrightarrow A_{S[1/r_0]}$ is isomorphic to the unit sheaf of modules on $U$. Assume that the pullbacks of $\mathcal L_1$ and $\mathcal L_2$ along the morphism $A_{S_{\mathfrak p}} \to A_{S[1/r_0]}$ induced by the identity on $A$ and by $\operatorname{Spec} \psi$ are isomorphic. Then there exist $r \in S$ with $r \notin \mathfrak p$ and a ring homomorphism $\psi_r : S[1/r_0] \to S[1/r]$ compatible with the structure maps from $S$, such that the pullbacks of $\mathcal L_1$ and $\mathcal L_2$ along the resulting morphism $A_{S[1/r]} \to A_{S[1/r_0]}$ are already isomorphic.
--
--   This is the spreading-out step for isomorphisms of line bundles: an isomorphism over the local ring $S_{\mathfrak p}$ descends to a basic open neighbourhood $D(r)$ of $\mathfrak p$ inside $D(r_0)$, in the style of EGA IV §8.5. It feeds the study of the relative Picard functor and of polarisations, and is used in the construction of canonical polarisation data on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    [QuasiCompact f] [QuasiSeparated f]
    (𝔭 : Ideal S) [𝔭.IsPrime] (r₀ : S) (hr₀ : r₀ ∉ 𝔭)
    (ψ : Localization.Away r₀ →+* Localization.AtPrime 𝔭)
    (hψ : ψ.comp (algebraMap S (Localization.Away r₀)) = algebraMap S (Localization.AtPrime 𝔭))
    (𝓛₁ 𝓛₂ : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀))))).Modules)
    (h₁ : Scheme.Modules.IsInvertible 𝓛₁) (h₂ : Scheme.Modules.IsInvertible 𝓛₂)
    (hiso : Nonempty
      ((Scheme.Modules.pullback
          (Limits.pullback.lift
            (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
            (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
              Spec.map (CommRingCat.ofHom ψ))
            (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
            Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ⟶
              Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀)))))).obj 𝓛₁ ≅
       (Scheme.Modules.pullback
          (Limits.pullback.lift
            (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
            (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
              Spec.map (CommRingCat.ofHom ψ))
            (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]))).obj 𝓛₂)) :
    ∃ (r : S) (_ : r ∉ 𝔭) (ψr : Localization.Away r₀ →+* Localization.Away r)
      (hψr : ψr.comp (algebraMap S (Localization.Away r₀)) = algebraMap S (Localization.Away r)),
      Nonempty
        ((Scheme.Modules.pullback
            (Limits.pullback.lift
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))))
              (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))) ≫
                Spec.map (CommRingCat.ofHom ψr))
              (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψr]) :
              Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))) ⟶
                Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀)))))).obj 𝓛₁ ≅
         (Scheme.Modules.pullback
            (Limits.pullback.lift
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))))
              (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))) ≫
                Spec.map (CommRingCat.ofHom ψr))
              (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψr]))).obj 𝓛₂) := by sorry
