-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_units_H1_classes
-- name    : AlgebraicGeometry.Scheme.exists_etale_units_H1_classes
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-18T19:13:46.316634+00:00
-- url     : https://prove2.me/theorems/7ac31989-3a94-4275-aa7f-61ce684dc109
-- title:
--   The Picard group as the first étale cohomology of units
-- statement:
--   For a scheme $X$, there is an assignment of classes in $H^1_{\mathrm{et}}(X, \mathbf G_m)$ to invertible modules on $X$. It is surjective, two classes coincide exactly when the modules are isomorphic, and tensor product corresponds to addition. The statement records equality of isomorphism classes in the monoid of module classes.
-- source:
--   Stacks Project, Theorem 59.24.1, https://stacks.math.columbia.edu/tag/03P8.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmallEtaleUnits

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.exists_etale_units_H1_classes (X : Scheme.{u}) :
    ∃ c : {M : X.Modules // Scheme.Modules.IsInvertible M} →
        (PhilipponKummerSequence.units X).H 1,
      Function.Surjective c ∧
      (∀ M N, c M = c N ↔ toSkeleton M.val = toSkeleton N.val) ∧
      ∀ M N P, toSkeleton P.val = toSkeleton M.val * toSkeleton N.val → c P = c M + c N := by sorry
