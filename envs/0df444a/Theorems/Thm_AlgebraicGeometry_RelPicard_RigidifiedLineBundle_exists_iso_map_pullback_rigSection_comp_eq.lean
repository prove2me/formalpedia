-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/7a106f50-329e-5d09-8567-9bffeaf531a0
-- title:
--   Normalising an isomorphism to respect the rigidifications
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme with a structure morphism $c \colon C \to \operatorname{Spec} R$, and let $\varepsilon$ be an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $T$ be a scheme with a morphism $t \colon T \to \operatorname{Spec} R$, and write $\varepsilon_T =$ `rigSection c t ε` for the morphism $T \to C \times_{\operatorname{Spec} R} T$ determined by $t$ followed by $\varepsilon$ in the first coordinate and $\mathrm{id}_T$ in the second. Let $M$ and $M'$ be rigidified line bundles on $C \times_{\operatorname{Spec} R} T$ relative to $c$, $\varepsilon$ and $t$: each consists of a module $M.L$ over the fibre product which is locally trivial (every point has an open neighbourhood $U$ on which the restriction of the module is isomorphic to the unit sheaf of $U$) together with the mere existence of an isomorphism $\varepsilon_T^{*}(M.L) \cong \mathcal{O}_T$. Let $\alpha \colon \varepsilon_T^{*}(M.L) \cong \mathcal{O}_T$ and $\alpha' \colon \varepsilon_T^{*}(M'.L) \cong \mathcal{O}_T$ be chosen such isomorphisms, and let $\varphi \colon M.L \cong M'.L$ be any isomorphism of modules on $C \times_{\operatorname{Spec} R} T$. Then there is an isomorphism $\varphi' \colon M.L \cong M'.L$ such that $\varepsilon_T^{*}(\varphi')$ followed by $\alpha'$ equals $\alpha$. The isomorphism produced is not asserted to be related to $\varphi$, which enters only as the hypothesis that the two underlying modules are isomorphic.
--
--   This is the standard observation that a rigidification removes the $\mathbb{G}_m$-ambiguity in isomorphisms of line bundles (Bosch–Lütkebohmert–Raynaud, Néron Models, 8.1): an abstract isomorphism of the underlying modules may be rescaled by a unit pulled back from the base so as to match the chosen trivialisations along the section. It is used in the construction of the relative Picard functor, in the descent statements for rigidified line bundles along affine flat surjections and finite faithfully flat morphisms and in the gluing statement over an open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (α' : (Scheme.Modules.pullback (rigSection c t ε)).obj M'.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (φ : M.L ≅ M'.L) :
    ∃ φ' : M.L ≅ M'.L, (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ' ≪≫ α' = α := by sorry
