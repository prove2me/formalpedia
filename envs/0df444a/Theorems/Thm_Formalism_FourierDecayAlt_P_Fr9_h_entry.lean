-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_h_entry
-- name    : Formalism.FourierDecayAlt.P.Fr9.h_entry
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:03:36.312976+00:00
-- url     : https://prove2.me/theorems/404fc852-cf2d-4441-ad91-8039a63fed1e
-- title:
--   Fr9: h entry
-- statement:
--   The Fr9 construction uses the h entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L516-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L516-L529

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
variable {L : LevelData A r} {f : FrameData S A}

theorem Formalism.FourierDecayAlt.P.Fr9.h_entry {X1 X2 : SlopeTestRemainingChoices S A} (h1 : ∀ g ∈ zfns L, Commute X1 (io g)) (h2 : ∀ g ∈ zfns L, Commute X2 (io g))
    (h12 : Commute X1 X2) (c q : ℂ) :
    io L.ζi * io L.GG * -(c⁻¹ • q • (io L.GGi * X1 * (io L.GGi * X2))) =
      -(kapL L * ((q / c) • (X2 * X1))) * io L.ζbi := by sorry
