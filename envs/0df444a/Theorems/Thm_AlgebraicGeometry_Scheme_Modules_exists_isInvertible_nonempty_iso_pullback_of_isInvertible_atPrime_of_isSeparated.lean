-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_iso_pullback_of_isInvertible_atPrime_of_isSeparated
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_iso_pullback_of_isInvertible_atPrime_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/0a9124b3-bc73-5bfe-a8a2-1ea55e672af7
-- title:
--   Invertible modules over S_𝔭 descend to a basic open
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme and let $f : A \to \operatorname{Spec} S$ be a quasi-compact separated morphism, and let $\mathfrak p$ be a prime ideal of $S$. Write $A_T$ for the fibre product $A \times_{\operatorname{Spec} S} \operatorname{Spec} T$ formed along $\operatorname{Spec}$ of the structure map $S \to T$. Let $\mathcal L$ be a module on $A_{S_{\mathfrak p}}$, where $S_{\mathfrak p} =$ `Localization.AtPrime 𝔭`, and assume $\mathcal L$ satisfies `Scheme.Modules.IsInvertible`, i.e. every point of $A_{S_{\mathfrak p}}$ has an open neighbourhood $U$ such that the restriction of $\mathcal L$ along the inclusion $U \hookrightarrow A_{S_{\mathfrak p}}$ is isomorphic to the unit sheaf of modules on $U$. Then there exist an element $r \in S$ with $r \notin \mathfrak p$, a ring homomorphism $\psi : S_r \to S_{\mathfrak p}$ from the localisation away from $r$ satisfying $\psi \circ (S \to S_r) = (S \to S_{\mathfrak p})$, and a module $\mathcal L_r$ on $A_{S_r}$, such that $\mathcal L_r$ is invertible in the same local-triviality sense and the pullback of $\mathcal L_r$ along the morphism $A_{S_{\mathfrak p}} \to A_{S_r}$ induced by the first projection together with the second projection followed by $\operatorname{Spec} \psi$ is isomorphic to $\mathcal L$ (the set of such isomorphisms being asserted nonempty).
--
--   This is the surjectivity half of the statement that $\operatorname{Pic}(A_{S_{\mathfrak p}})$ is the colimit of $\operatorname{Pic}(A_{S_r})$ over $r \notin \mathfrak p$: an invertible module on the fibre over the local ring at $\mathfrak p$ already exists over some basic open neighbourhood of $\mathfrak p$. It is used to spread out line bundles and polarisation data from a local base to a Zariski-open base, in the constructions of fake elliptic curves with canonical polarisation data and in the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_iso_pullback_of_isInvertible_atPrime_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_iso_pullback_of_isInvertible_atPrime_of_isSeparated
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    [QuasiCompact f] [IsSeparated f]
    (𝔭 : Ideal S) [𝔭.IsPrime]
    (𝓛 : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))).Modules)
    (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (r : S) (_ : r ∉ 𝔭) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
      (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭))
      (𝓛r : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).Modules),
      Scheme.Modules.IsInvertible 𝓛r ∧
      Nonempty
        ((Scheme.Modules.pullback
            (Limits.pullback.lift
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
              (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
                Spec.map (CommRingCat.ofHom ψ))
              (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
              Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ⟶
                Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))))).obj 𝓛r ≅ 𝓛) := by sorry
