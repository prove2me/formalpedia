-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_comm_sc
-- name    : Formalism.FourierDecayAlt.P.Fr7.comm_sc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:33.744575+00:00
-- url     : https://prove2.me/theorems/ff7b7968-505f-42d6-b6c5-eeaaaecc6a9d
-- title:
--   Fr7: comm sc
-- statement:
--   The Fr7 construction uses the comm sc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L177-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L177-L179

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
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {a : S}

theorem Formalism.FourierDecayAlt.P.Fr7.comm_sc {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) (φ : ℂ) :
    Commute b (ins a !![φ • (1 : SlopeTestRemainingChoices S A), 0; 0, 1]) := by sorry
