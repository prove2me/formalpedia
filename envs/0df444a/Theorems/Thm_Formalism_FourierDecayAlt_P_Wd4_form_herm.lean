-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_form_herm
-- name    : Formalism.FourierDecayAlt.P.Wd4.form_herm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:35.095255+00:00
-- url     : https://prove2.me/theorems/11909a95-9746-4051-a432-0c5313227f8f
-- title:
--   Wd4: form herm
-- statement:
--   The Wd4 construction uses the form herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L388-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L388-L392

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd4.form_herm {a : S} {RR : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)} (hRR : FreeOf a RR) (hT : FreeOf2 a T)
    (h : (d0 RR * T)ᴴ = d0 RR * T) : star (RR * ins a T) = RR * ins a T := by sorry
