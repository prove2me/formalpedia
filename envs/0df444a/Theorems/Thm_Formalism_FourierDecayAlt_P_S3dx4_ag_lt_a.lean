-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ag_lt_a
-- name    : Formalism.FourierDecayAlt.P.S3dx4.ag_lt_a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:36:51.352209+00:00
-- url     : https://prove2.me/theorems/a69e938a-153c-49ee-a6c0-e26343e904f2
-- title:
--   S3dx4: ag lt a
-- statement:
--   The S3dx4 construction uses the ag lt a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiRegOf.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiRegOf.lean#L14-L18

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L1QuotientIntegralBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem Formalism.FourierDecayAlt.P.S3dx4.ag_lt_a {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : AG k r < aOf r h := by sorry
