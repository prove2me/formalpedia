-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_gap4
-- name    : Formalism.FourierDecayAlt.P.S3dx4.gap4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:56:23.855135+00:00
-- url     : https://prove2.me/theorems/16c4cc90-4a9a-4e43-830d-79e1c57aaf6b
-- title:
--   S3dx4: gap4
-- statement:
--   The S3dx4 construction uses the gap4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbConvDDOfDecDD.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbConvDDOfDecDD.lean#L16-L17

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CkOnZeroOfContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbConvDDOfDecDD
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
open scoped InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem Formalism.FourierDecayAlt.P.S3dx4.gap4 {k r : ℕ} {h : ℝ} (hG : GapOK k r h) :
    9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3 ≤ aOf r h := by sorry
