-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_line_bundle_power_cosets_of_isProper
-- name    : AlgebraicGeometry.RelPicard.exists_finite_line_bundle_power_cosets_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-18T18:10:41.491682+00:00
-- url     : https://prove2.me/theorems/97300f05-1201-4597-97be-2d416fdff9cc
-- title:
--   Finite Picard quotient modulo a tensor power on a proper scheme
-- statement:
--   Let X be proper over an algebraically closed field. For some integer p > 1, there are finitely many line bundles M_i on X such that every line bundle N is isomorphic to M_i tensored with the p-th tensor power of a line bundle on X. The equality in the statement is in the monoid of isomorphism classes of modules.
-- source:
--   Choose a prime invertible in the base field. The étale Kummer sequence embeds Pic(X)/pPic(X) in H^2_et(X, mu_p) (Stacks Project, https://stacks.math.columbia.edu/tag/03PK). The latter is finite by proper étale finiteness (SGA 4, Exposé XIV, Corollaire 1.2, https://grothendiecksga.com/read/sga4/en/XIV-1.html).

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.RelPicard.exists_finite_line_bundle_power_cosets_of_isProper
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (p r : ℕ) (M : Fin r → X.Modules),
      1 < p ∧ (∀ i, Scheme.Modules.IsInvertible (M i)) ∧
        ∀ N : X.Modules, Scheme.Modules.IsInvertible N →
          ∃ (i : Fin r) (P : X.Modules), Scheme.Modules.IsInvertible P ∧
            toSkeleton N = toSkeleton (M i) * toSkeleton P ^ p := by sorry
