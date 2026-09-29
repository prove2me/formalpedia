-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_hom_eq_of_pullback_section_trivial
-- name    : AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_hom_eq_of_pullback_section_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/3cfde747-ff0d-5368-924f-3d97446e420c
-- title:
--   Lifting automorphisms of a module along a section
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme, and let $f : A \to \operatorname{Spec} S$ be a morphism admitting a section $e : \operatorname{Spec} S \to A$, in the sense that $e$ followed by $f$ is the identity of $\operatorname{Spec} S$. Let $N$ be a sheaf of modules on $A$ (an object of `A.Modules`), and assume that the pullback $e^{*}N$, formed by the functor `Scheme.Modules.pullback e`, is isomorphic to the unit sheaf of modules `SheafOfModules.unit` on $\operatorname{Spec} S$ — that is, the type of such isomorphisms is nonempty, no particular trivialisation being fixed. Then for every isomorphism $\mu$ of $e^{*}N$ with itself there is an isomorphism $\theta : N \cong N$ in `A.Modules` whose pullback along $e$ has underlying morphism equal to that of $\mu$: $(e^{*}\theta) = \mu$ as morphisms $e^{*}N \to e^{*}N$. No invertibility or coherence assumption is imposed on $N$ beyond the triviality of $e^{*}N$, and the conclusion equates the two morphisms, not merely the two isomorphisms up to something.
--
--   This is the rigidification lemma that automorphisms of a module trivial along a section of $f$ are realised by automorphisms of the module itself, the triviality being used to identify $\operatorname{Aut}(e^{*}N)$ with the units of $S$ and $f$ with the mechanism transporting them to $A$. It is used in the theory of rigidified line bundles and polarisations on abelian schemes, where it underlies the comparison of isomorphisms of line bundles with isomorphisms respecting rigidifications.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_hom_eq_of_pullback_section_trivial.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_hom_eq_of_pullback_section_trivial
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (N : A.Modules)
    (hNe : Nonempty ((Scheme.Modules.pullback e).obj N ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (μ : (Scheme.Modules.pullback e).obj N ≅ (Scheme.Modules.pullback e).obj N) :
    ∃ θ : N ≅ N, (Scheme.Modules.pullback e).map θ.hom = μ.hom := by sorry
