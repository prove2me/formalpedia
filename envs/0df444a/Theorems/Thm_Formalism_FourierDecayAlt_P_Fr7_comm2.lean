-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_comm2
-- name    : Formalism.FourierDecayAlt.P.Fr7.comm2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:40.919394+00:00
-- url     : https://prove2.me/theorems/54d4a0ec-64ca-4791-9e9c-b02a4f5e3805
-- title:
--   Fr7: comm2
-- statement:
--   The Fr7 construction uses the comm2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L144-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L144-L147

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

theorem Formalism.FourierDecayAlt.P.Fr7.comm2 {b p q s t : SlopeTestRemainingChoices S A} (hp : Commute b p) (hq : Commute b q) (hs : Commute b s) (ht : Commute b t) :
    ∀ i j, Commute b ((!![p, q; s, t] : M2 (SlopeTestRemainingChoices S A)) i j) := by sorry
