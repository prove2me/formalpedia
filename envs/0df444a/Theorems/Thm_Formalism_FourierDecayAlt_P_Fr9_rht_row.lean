-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_rht_row
-- name    : Formalism.FourierDecayAlt.P.Fr9.rht_row
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:02:37.651628+00:00
-- url     : https://prove2.me/theorems/704ad207-0943-4f25-94bf-f484c32d1e1e
-- title:
--   Fr9: rht row
-- statement:
--   The Fr9 construction uses the rht row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L25-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L25-L46

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

theorem Formalism.FourierDecayAlt.P.Fr9.rht_row (b : S) (d : ℂ) (T : M2 (SlopeTestRemainingChoices S A)) (j : Fin 2) :
    (Rht0 b d * T : M2 (SlopeTestRemainingChoices S A)) 1 j =
      ins b ((d - 1)⁻¹ • !![d • T 1 j, 0; -T 0 j, (d - 1) • T 1 j]) := by sorry
