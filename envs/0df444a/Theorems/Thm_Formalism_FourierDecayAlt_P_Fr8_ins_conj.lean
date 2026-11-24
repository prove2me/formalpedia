-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_ins_conj
-- name    : Formalism.FourierDecayAlt.P.Fr8.ins_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:04:39.536153+00:00
-- url     : https://prove2.me/theorems/0430f5b3-483b-4a96-8d56-70a6a32f8921
-- title:
--   Fr8: ins conj
-- statement:
--   The Fr8 construction uses the ins conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L124-L131

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Fr8.ins_conj (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (P Q : SlopeTestRemainingChoices S A) (hP : FreeOf a P) :
    ins a (M.map fun b => P * b * Q) = P * ins a M * Q := by sorry
