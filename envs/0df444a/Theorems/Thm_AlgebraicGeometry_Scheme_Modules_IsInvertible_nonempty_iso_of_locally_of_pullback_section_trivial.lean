-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_locally_of_pullback_section_trivial
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_locally_of_pullback_section_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/473229a7-17bf-5e5a-bd0e-a883736b05b1
-- title:
--   Locally isomorphic rigidified invertible modules are isomorphic
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, and $f : A \to \operatorname{Spec} S$ a morphism admitting a section $e : \operatorname{Spec} S \to A$, so that $e$ followed by $f$ is the identity. Assume that for every $r \in S$ the ring map on global sections induced by the projection $A \times_{\operatorname{Spec} S} \operatorname{Spec} S[1/r] \to \operatorname{Spec} S[1/r]$ (the second pullback projection of $f$ against $\operatorname{Spec}$ of the localisation map $S \to S[1/r]$, with $S[1/r] =$ `Localization.Away r`) is surjective; that is, every global function on $A \times_{\operatorname{Spec} S} \operatorname{Spec} S[1/r]$ is pulled back from $S[1/r]$. Let $L$ and $M$ be modules over $A$ which are invertible in the sense that every point of $A$ has an open neighbourhood $U$ with the restriction of the module along the inclusion $U \hookrightarrow A$ isomorphic to the unit sheaf of modules on $U$. Assume the pullbacks $e^{*}L$ and $e^{*}M$ are each isomorphic to the unit sheaf of modules on $\operatorname{Spec} S$, and that $L$ and $M$ are isomorphic locally on the base: every point $s$ of $\operatorname{Spec} S$ lies in an open $U$ such that the restrictions of $L$ and $M$ along the inclusion $f^{-1}U \hookrightarrow A$ are isomorphic. Then $L$ and $M$ are isomorphic as modules over $A$; the conclusion asserts only that the type of such isomorphisms is nonempty.
--
--   This is the existence half of Zariski gluing for rigidified line bundles on a scheme over an affine base: triviality along the section pins down a local isomorphism uniquely, so local-on-the-base isomorphisms can be glued. It is used in the construction of the relative Picard and polarisation data for abelian schemes, notably in the descent and Čech-nerve arguments for polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_locally_of_pullback_section_trivial.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_locally_of_pullback_section_trivial
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (hΓ : ∀ r : S, Function.Surjective
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom)
    (L M : A.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (hLe : Nonempty ((Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (hMe : Nonempty ((Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (hloc : ∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    Nonempty (L ≅ M) := by sorry
