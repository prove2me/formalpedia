-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_mat2
-- name    : Formalism.FourierDecayAlt.P.Fr7.mat2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:40.574297+00:00
-- url     : https://prove2.me/theorems/91839064-7b56-4940-a124-31785f76bf36
-- title:
--   Fr7: mat2
-- statement:
--   The Fr7 construction uses the mat2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L45-L56

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1

theorem Formalism.FourierDecayAlt.P.Fr7.mat2 {B : Type} [Ring B] (z zi w wi G Gi l : B) (hz : z * zi = 1) (hw : w * wi = 1)
    (hG : Gi * G = 1) :
    (!![1, 0; -l, Gi] * !![z, 0; 0, w]) * (!![zi, 0; 0, wi] * !![1, 0; G * l, G]) = 1 := by sorry
