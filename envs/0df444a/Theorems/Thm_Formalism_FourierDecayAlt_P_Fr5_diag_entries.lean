-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_diag_entries
-- name    : Formalism.FourierDecayAlt.P.Fr5.diag_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:04.4638+00:00
-- url     : https://prove2.me/theorems/e5a7f1e3-08a4-4fa4-877b-e1fbec616300
-- title:
--   Fr5: diag entries
-- statement:
--   The Fr5 construction uses the diag entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L374-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L374-L382

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Fr5.diag_entries (p1 p2 w c1 c2 e1 e2 : SlopeTestRemainingChoices S A) :
    !![p1, 0; 0, p2] * d0 w * !![c1, 0; 0, c2] * !![e1, 0; 0, e2] =
      !![p1 * w * c1 * e1, 0; 0, p2 * w * c2 * e2] := by sorry
