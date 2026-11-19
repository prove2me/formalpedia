-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_units_frame_torsors
-- name    : AlgebraicGeometry.Scheme.exists_etale_units_frame_torsors
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-18T21:40:59.865202+00:00
-- url     : https://prove2.me/theorems/24d109d6-4c9a-4953-8821-2cd37979e6d3
-- title:
--   Étale frame torsors and descent of invertible modules
-- statement:
--   On the small étale site of any scheme $X$, line bundle frames define torsors under the sheaf of units. Every such torsor is equivariantly isomorphic to one of these frame torsors, and the frame torsors of two invertible modules are equivariantly isomorphic exactly when the modules are isomorphic. A tensor-product isomorphism gives a natural map from pairs of frames to frames of the product, which multiplies the units measuring changes of frames.
-- source:
--   Stacks Project, Sections 59.24 and 21.6, https://stacks.math.columbia.edu/tag/03P8 and https://stacks.math.columbia.edu/tag/040D, and Proposition 35.5.2, https://stacks.math.columbia.edu/tag/023T.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmallEtaleUnits
import Definitions.Def_AlgebraicGeometry_AbelianSheafTorsors

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison PhilipponTorsorClassification
universe u

theorem AlgebraicGeometry.Scheme.exists_etale_units_frame_torsors (X : Scheme.{u}) :
    ∃ F : {M : X.Modules // Scheme.Modules.IsInvertible M} → Torsor (PhilipponKummerSequence.units X),
      (∀ A : Torsor (PhilipponKummerSequence.units X), ∃ M, Equivalent (F M) A) ∧
      (∀ M N, Equivalent (F M) (F N) ↔ toSkeleton M.val = toSkeleton N.val) ∧
      ∀ M N P, toSkeleton P.val = toSkeleton M.val * toSkeleton N.val →
        Combines (F M) (F N) (F P) := by sorry
