-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free2
-- name    : Formalism.FourierDecayAlt.P.Fr7.free2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:35.071032+00:00
-- url     : https://prove2.me/theorems/c25a8131-4db2-4b10-a1d7-8b29352127e4
-- title:
--   Fr7: free2
-- statement:
--   The Fr7 construction uses the free2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L134-L137

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

theorem Formalism.FourierDecayAlt.P.Fr7.free2 {p q s t : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) (hs : FreeOf a s) (ht : FreeOf a t) :
    FreeOf2 a !![p, q; s, t] := by sorry
