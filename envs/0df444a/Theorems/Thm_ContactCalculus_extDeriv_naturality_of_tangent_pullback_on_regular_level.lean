-- Prove2me | Theorems.Thm_ContactCalculus_extDeriv_naturality_of_tangent_pullback_on_regular_level
-- name    : ContactCalculus.extDeriv_naturality_of_tangent_pullback_on_regular_level
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T15:57:51.929289+00:00
-- url     : https://prove2.me/theorems/fdb26b16-0a70-4e57-908d-d67754cf342f
-- title:
--   Exterior differentiation respects tangent pullback on regular levels
-- statement:
--   Let M be the regular zero level of a smooth map F from real n-space to real c-space. Let f be a smooth map from real n-space to real m-space, and let alpha and beta be smooth ambient one-forms on the target and source spaces. Assume alpha at f(z), applied to Df at z of any tangent vector, equals beta at z of that vector for every z in M. Then for all tangent vectors u and v at y in M, d alpha at f(y), evaluated on Df(u) and Df(v), equals d beta at y evaluated on u and v. This does not require f to preserve a level set, have injective differential, or be globally bijective.
-- source:
--   Naturality of exterior differentiation, d(f*alpha)=f*(d alpha), applied to the restriction of f to a regular level. Geiges, Contact Geometry, https://arxiv.org/pdf/math/0307242, Definition 2.5 and Remark 2.21(1); Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Analysis/Calculus/DifferentialForm/Basic.lean, extDeriv_pullback. The regular-level formulation is a derived generalization, not a verbatim statement in Geiges.

import Definitions.Def_GrayStability_Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
open GrayStability
open scoped ContDiff

theorem ContactCalculus.extDeriv_naturality_of_tangent_pullback_on_regular_level
    {n c m : ℕ} (F : E n → E c) (hF : ContDiff ℝ ∞ F)
    (hreg : ∀ z ∈ levelSet F, Function.Surjective (fderiv ℝ F z))
    (α : OneForm m) (β : OneForm n)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (f : E n → E m) (hf : ContDiff ℝ ∞ f)
    (hpull : ∀ z ∈ levelSet F, ∀ v ∈ tangentSpace F z,
      α (f z) (fderiv ℝ f z v) = β z v)
    (y : E n) (hy : y ∈ levelSet F) (u v : E n)
    (hu : u ∈ tangentSpace F y) (hv : v ∈ tangentSpace F y) :
    extDerivOneForm α (f y) (fderiv ℝ f y u) (fderiv ℝ f y v) =
      extDerivOneForm β y u v := by sorry
