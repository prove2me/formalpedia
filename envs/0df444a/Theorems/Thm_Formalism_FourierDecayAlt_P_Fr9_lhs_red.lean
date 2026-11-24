-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_lhs_red
-- name    : Formalism.FourierDecayAlt.P.Fr9.lhs_red
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:02:48.406392+00:00
-- url     : https://prove2.me/theorems/eb4b0c96-5bb4-48a2-9826-138c376e664d
-- title:
--   Fr9: lhs red
-- statement:
--   The Fr9 construction uses the lhs red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L270-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L270-L272

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
variable {b : S}

theorem Formalism.FourierDecayAlt.P.Fr9.lhs_red {F : SlopeTestRemainingChoices S A} (hF : FreeOf b F) {P N Nh : M2 (SlopeTestRemainingChoices S A)} (hP : FreeOf2 b P)
    (hN : d0 F * N = Nh * d0 F) : ins b P * F * ins b N = ins b (P * Nh * d0 F) := by sorry
