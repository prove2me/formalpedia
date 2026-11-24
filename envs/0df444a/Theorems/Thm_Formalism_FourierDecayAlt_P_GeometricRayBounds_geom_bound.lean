-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GeometricRayBounds_geom_bound
-- name    : Formalism.FourierDecayAlt.P.GeometricRayBounds.geom_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:14:01.651049+00:00
-- url     : https://prove2.me/theorems/c509e8d8-d8dd-43d0-8502-b8d71f4cf68f
-- title:
--   Geometric Ray Bounds: geom bound
-- statement:
--   The Geometric Ray Bounds construction uses the geom bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragingVanishes.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragingVanishes.lean#L41-L49

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragingVanishes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GeometricRayBounds

theorem Formalism.FourierDecayAlt.P.GeometricRayBounds.geom_bound (q : ℂ) (hq : ‖q‖ = 1) (hq1 : q ≠ 1) (M : ℕ) :
    ‖∑ m ∈ range M, q ^ m‖ ≤ 2 / ‖q - 1‖ := by sorry
