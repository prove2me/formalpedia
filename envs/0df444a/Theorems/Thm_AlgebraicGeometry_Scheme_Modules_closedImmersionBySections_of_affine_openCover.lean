-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_closedImmersionBySections_of_affine_openCover
-- name    : AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_affine_openCover
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-07T14:40:38.330124+00:00
-- url     : https://prove2.me/theorems/b6727fd7-4060-4428-a497-b95eed04b6a2
-- title:
--   Closed presentations descend from an affine atlas of an affine base
-- statement:
--   Let $S$ be a commutative ring, let $f:X\to\operatorname{Spec}S$ be proper, and let $M$ be an invertible $\mathcal O_X$-module. Let $\{U_i\to\operatorname{Spec}S\}$ be any open cover by affine schemes. For each $i$, choose a cartesian model $V_i=X\times_{\operatorname{Spec}S}U_i$, with its open immersion $j_i:V_i\to X$ and projection $f_i:V_i\to U_i$.
--
--   Suppose that the actual restricted module $j_i^*M$ admits a closed projective presentation over $\Gamma(U_i,\mathcal O_{U_i})$ for every $i$. Then there exist an integer $N$ and a projective presentation of $M$ whose map $X\hookrightarrow\mathbb P^N_S$ is a closed immersion and whose projection is exactly $f$.
--
--   The atlas and the dimensions of its local presentations need not be finite. The proof constructs a finite principal refinement and derives its unit-ideal condition. No Noetherian, integral, reduced or nonemptiness assumption is imposed. The restriction and pullback comparisons use the same global module $M$ throughout.
-- source:
--   Derived affine-atlas formulation of the public Proved principal-cover descent theorem https://prove2.me/theorems/909a009d-1f23-5a0b-8a4b-6a0bb18d473b , together with native projective base change https://prove2.me/theorems/040eceda-1925-55bf-adcc-b73e83e4440a and module-isomorphism transport https://prove2.me/theorems/241df6ce-75a9-54a6-b267-0f889f46d5e6 . The finite principal refinement, its unit-ideal condition and the actual module comparisons are proved in the submitted solution. Applied to the glued nodal Cartier-center module, this supplies global projectivity over an affine base in the Philippon alteration development; projectivity over a nonaffine projective base and the full alteration theorem remain further work.

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v

theorem AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_affine_openCover {S : Type u} [CommRing S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (hf : IsProper f)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (𝒰 : Scheme.OpenCover.{v} (Spec (CommRingCat.of S))) [∀ i, IsAffine (𝒰.X i)]
    (V : 𝒰.I₀ → Scheme.{u}) (iV : ∀ i, V i ⟶ X) (fV : ∀ i, V i ⟶ 𝒰.X i)
    [∀ i, IsOpenImmersion (iV i)]
    (sq : ∀ i, IsPullback (iV i) (fV i) f (𝒰.f i))
    (h : ∀ i, Scheme.Modules.ClosedImmersionBySections (M.restrict (iV i))
      (fV i ≫ (𝒰.X i).toSpecΓ)) : Scheme.Modules.ClosedImmersionBySections M f := by sorry
