-- Prove2me | Theorems.Thm_AlgebraicGeometry_finrank_sections_pushforward_thickening_and_injective_unit_app_iff
-- name    : AlgebraicGeometry.finrank_sections_pushforward_thickening_and_injective_unit_app_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/5d20956e-dd46-58ec-ba64-69a2e61cfb73
-- title:
--   Sections of L(rσ) on the n-th neighbourhood of σ
-- statement:
--   Let $K$ be a field and $X$ a scheme equipped with a morphism $x : X \to \operatorname{Spec} K$ that is separated and smooth of relative dimension $1$, and let $\sigma : \operatorname{Spec} K \to X$ be a section of $x$, i.e. $\sigma$ followed by $x$ is the identity. Let $L$ be a module on $X$ that is invertible in the sense that every point of $X$ has an open neighbourhood $U$ over which the pullback of $L$ along $U \hookrightarrow X$ is isomorphic to the unit module of $U$. Let $r, n, d$ be natural numbers with $d + n = r$. Write $\mathcal I = \sigma.\mathrm{ker}$ for the ideal sheaf data of $\sigma$; for an ideal sheaf $I$, `invModule` is the dual of the module `module` attached to $I$, namely the kernel of the map from the unit module to the pushforward of the unit module along the closed immersion $V(I) \hookrightarrow X$. Put $G = L \otimes (\mathcal I^{\,r})^{\mathrm{inv}}$, let $i$ be the closed immersion $V(\mathcal I^{\,n}) \hookrightarrow X$, and let $\eta : G \to i_* i^* G$ be the unit of the pullback–pushforward adjunction along $i$, evaluated at $G$. The global sections over $\top$ are given the $K$-module structure coming from $x$, through the $K$-algebra structure on $\Gamma(X, \top)$ induced by $x$. The conclusion is twofold: first, $\Gamma(i_* i^* G, \top)$ is a finite $K$-module and $\dim_K \Gamma(i_* i^* G, \top) = n$; second, the map $\Gamma(\eta, \top)$ on sections over $\top$ is injective if and only if $\Gamma(L \otimes (\mathcal I^{\,d})^{\mathrm{inv}}, \top)$ is a subsingleton.
--
--   This is the evaluation of a line bundle $L(r\sigma)$ on the $n$-th infinitesimal neighbourhood of a rational point of a smooth curve: the target of the evaluation map has dimension exactly $n$, and the map is injective on global sections precisely when $L(d\sigma)$ with $d = r - n$ has no nonzero global section. It is used in the construction of theta bundles and the rigidified line bundles that enter the relative Picard functor, via [`AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_eq_zero_iff`](thm.html#AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_eq_zero_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finrank_sections_pushforward_thickening_and_injective_unit_app_iff.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.finrank_sections_pushforward_thickening_and_injective_unit_app_iff
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsSeparated x] [SmoothOfRelativeDimension 1 x]
    (σ : Spec (CommRingCat.of K) ⟶ X) (hσ : σ ≫ x = 𝟙 _)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (r n d : ℕ) (hd : d + n = r) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x
      ((Scheme.Modules.pushforward ((σ.ker ^ n).subschemeι)).obj
        ((Scheme.Modules.pullback ((σ.ker ^ n).subschemeι)).obj (L ⊗ (σ.ker ^ r).invModule))) ⊤
    (Module.Finite K Γ((Scheme.Modules.pushforward ((σ.ker ^ n).subschemeι)).obj
          ((Scheme.Modules.pullback ((σ.ker ^ n).subschemeι)).obj (L ⊗ (σ.ker ^ r).invModule)), ⊤) ∧
      Module.finrank K Γ((Scheme.Modules.pushforward ((σ.ker ^ n).subschemeι)).obj
          ((Scheme.Modules.pullback ((σ.ker ^ n).subschemeι)).obj (L ⊗ (σ.ker ^ r).invModule)), ⊤) = n) ∧
    (Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction ((σ.ker ^ n).subschemeι)).unit.app
          (L ⊗ (σ.ker ^ r).invModule)).app ⊤) ↔
        Subsingleton Γ(L ⊗ (σ.ker ^ d).invModule, ⊤)) := by sorry
