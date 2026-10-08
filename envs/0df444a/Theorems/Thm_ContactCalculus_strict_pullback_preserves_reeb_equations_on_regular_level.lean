-- Prove2me | Theorems.Thm_ContactCalculus_strict_pullback_preserves_reeb_equations_on_regular_level
-- name    : ContactCalculus.strict_pullback_preserves_reeb_equations_on_regular_level
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T15:38:53.298897+00:00
-- url     : https://prove2.me/theorems/6fa01f82-c293-4eec-a498-8ebb3cb19ad7
-- title:
--   Strict pullback transports normalized characteristic vectors on a regular level set
-- statement:
--   Let M be the zero level of a smooth map F from real n-space to real c-space, with surjective differential at every point of M. Let alpha and beta be smooth ambient one-forms. Suppose a smooth map f preserves M, its differential is injective on every tangent space of M, and f pulls alpha back to beta on those tangent spaces. If a tangent vector u at y has beta value one and lies in the nullspace of d beta restricted to the tangent space, then Df_y u is tangent at f(y), has alpha value one, and lies in the nullspace of d alpha restricted to the target tangent space. Contact nondegeneracy and global bijectivity of f are not required. This theorem is a general geometric prerequisite for the explicit Hopf naturality calculation.
-- source:
--   Geiges, Contact Geometry, https://arxiv.org/pdf/math/0307242, Definition 2.5 and Remark 2.21(1), printed p. 15. General regular-level formulation of strict Reeb naturality, derived from naturality of exterior differentiation and tangent differential bijectivity; no contact nondegeneracy is needed for preservation of the defining equations.

import Definitions.Def_GrayStability_Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
open GrayStability
open scoped ContDiff

theorem ContactCalculus.strict_pullback_preserves_reeb_equations_on_regular_level
    {n c : ℕ} (F : E n → E c) (hF : ContDiff ℝ ∞ F)
    (hreg : ∀ z ∈ levelSet F, Function.Surjective (fderiv ℝ F z))
    (α β : OneForm n) (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (f : E n → E n) (hf : ContDiff ℝ ∞ f)
    (hmap : Set.MapsTo f (levelSet F) (levelSet F))
    (hinj : ∀ z ∈ levelSet F, Set.InjOn (fderiv ℝ f z) (tangentSpace F z))
    (hpull : ∀ z ∈ levelSet F, ∀ v ∈ tangentSpace F z,
      pullback f α z v = β z v)
    (y : E n) (hy : y ∈ levelSet F) (u : E n)
    (hu : u ∈ tangentSpace F y) (hnorm : β y u = 1)
    (hker : ∀ v ∈ tangentSpace F y, extDerivOneForm β y u v = 0) :
    fderiv ℝ f y u ∈ tangentSpace F (f y) ∧
      α (f y) (fderiv ℝ f y u) = 1 ∧
      ∀ w ∈ tangentSpace F (f y),
        extDerivOneForm α (f y) (fderiv ℝ f y u) w = 0 := by sorry
