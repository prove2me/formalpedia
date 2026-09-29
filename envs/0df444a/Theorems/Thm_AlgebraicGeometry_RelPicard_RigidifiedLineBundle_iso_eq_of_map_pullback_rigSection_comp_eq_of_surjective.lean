-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/4f0616ac-b33f-5b7e-9000-26c75043c9f9
-- title:
--   Rigidity of isomorphisms of rigidified line bundles
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c : C \to \operatorname{Spec} R$ a morphism, and $\varepsilon$ an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, that is a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $t : T \to \operatorname{Spec} R$ be a further $R$-scheme, and assume that the ring homomorphism on global sections induced by the second projection $\mathrm{pullback.snd}\, c\, t : C \times_{\operatorname{Spec} R} T \to T$ is surjective. Let $M, M'$ be rigidified line bundles for the data $(c,\varepsilon,t)$: each consists of a sheaf of modules $L$ on $C \times_{\operatorname{Spec} R} T$ which is invertible in the sense that every point has an open neighbourhood $U$ over which the restriction of $L$ is isomorphic to the unit sheaf of modules of $U$, together with the (mere) existence of an isomorphism between the pullback of $L$ along $\mathrm{rigSection}\, c\, t\, \varepsilon : T \to C \times_{\operatorname{Spec} R} T$ (the morphism with components $t \circ \varepsilon$ and $\mathrm{id}_T$) and the unit sheaf of modules on $T$. Let $\alpha$ and $\alpha'$ be such isomorphisms for $M$ and $M'$ respectively, and let $\varphi, \psi : M.L \cong M'.L$ be isomorphisms whose pullbacks along $\mathrm{rigSection}\, c\, t\, \varepsilon$, followed by $\alpha'$, both equal $\alpha$. Then $\varphi = \psi$.
--
--   This is the rigidity lemma underlying the representability theory of the relative Picard functor: a rigidification along a section kills all automorphisms of an invertible sheaf, provided global functions on $C \times_{\operatorname{Spec} R} T$ come from $T$. It is the surjectivity-hypothesis form of the statement, and is cited by [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq), where the hypothesis on global sections is supplied from geometric assumptions on $c$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (hp : Function.Surjective (pullback.snd c t).appTop)
    (M M' : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (α' : (Scheme.Modules.pullback (rigSection c t ε)).obj M'.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (φ ψ : M.L ≅ M'.L)
    (hφ : (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ ≪≫ α' = α)
    (hψ : (Scheme.Modules.pullback (rigSection c t ε)).mapIso ψ ≪≫ α' = α) :
    φ = ψ := by sorry
