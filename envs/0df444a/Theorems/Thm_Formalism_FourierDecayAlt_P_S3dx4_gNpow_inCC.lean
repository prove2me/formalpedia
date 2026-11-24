-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_gNpow_inCC
-- name    : Formalism.FourierDecayAlt.P.S3dx4.gNpow_inCC
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:01.379216+00:00
-- url     : https://prove2.me/theorems/0aee5e69-f8d0-49c0-9178-34f4cca92b19
-- title:
--   S3dx4: g Npow in CC
-- statement:
--   The S3dx4 construction uses the g Npow in CC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MapInvMEq.lean#L24-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MapInvMEq.lean#L24-L40

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.S3dx4.gNpow_inCC (hNI : NormInv) (b : ℝ) (hb : b ≠ 0) :
    B.InCC b 0 (fun g : B.Mat k r => ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by sorry
