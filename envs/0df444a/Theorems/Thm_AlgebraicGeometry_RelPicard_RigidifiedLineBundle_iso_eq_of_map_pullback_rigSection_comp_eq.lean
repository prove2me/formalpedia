-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/2a21a34f-2198-5536-90bb-47f373552e6a
-- title:
--   Rigidity of isomorphisms of rigidified line bundles
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme and let $c \colon C \to \operatorname{Spec} R$ be a morphism, and let $\varepsilon$ be an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, that is, a morphism $\operatorname{Spec} R \to C$ together with a proof that $\varepsilon$ followed by $c$ is the identity of $\operatorname{Spec} R$. Assume the cohomological hypothesis `hH0`: for every $R$-algebra $A$, the structure map from $A$ to $\Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \top)$ — the $A$-algebra structure on the global sections being the one induced by the second projection of the pullback via `Scheme.TwoAffineOpenCover.algebraOfHom` — is bijective. Let $T$ be a scheme with a morphism $t \colon T \to \operatorname{Spec} R$, and let $M$, $M'$ be rigidified line bundles for $c$, $\varepsilon$ over $t$: each consists of a module $L$ on the pullback $C \times_{\operatorname{Spec} R} T$ which is locally trivial (every point has an open neighbourhood $U$ on which the restriction of $L$ is isomorphic to the unit sheaf of $U$), together with the nonemptiness of the set of isomorphisms between the pullback of $L$ along `rigSection c t ε` (the morphism $T \to C \times_{\operatorname{Spec} R} T$ with components $t$ followed by $\varepsilon$, and $\mathrm{id}_T$) and the unit sheaf on $T$. Let $\alpha$ and $\alpha'$ be such trivialisations along `rigSection c t ε` for $M.L$ and $M'.L$ respectively, and let $\varphi, \psi \colon M.L \cong M'.L$ be isomorphisms such that the pullback of $\varphi$ along `rigSection c t ε` followed by $\alpha'$ equals $\alpha$, and likewise for $\psi$. Then $\varphi = \psi$.
--
--   This is the rigidity statement for rigidified line bundles: a line bundle rigidified along the section $\varepsilon$ has no isomorphisms other than one respecting the chosen rigidifications, here under the universal hypothesis $c_*\mathcal{O} = \mathcal{O}$ expressed on affine test schemes. It is the uniqueness half of the representability analysis of the relative Picard functor, and is used by the statements producing isomorphisms of rigidified line bundles after pullback along open covers, along finite faithfully flat maps, and along affine flat surjections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (α' : (Scheme.Modules.pullback (rigSection c t ε)).obj M'.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (φ ψ : M.L ≅ M'.L)
    (hφ : (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ ≪≫ α' = α)
    (hψ : (Scheme.Modules.pullback (rigSection c t ε)).mapIso ψ ≪≫ α' = α) :
    φ = ψ := by sorry
