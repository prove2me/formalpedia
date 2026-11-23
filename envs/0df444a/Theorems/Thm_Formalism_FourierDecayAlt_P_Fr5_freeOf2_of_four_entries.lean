-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_freeOf2_of_four_entries
-- name    : Formalism.FourierDecayAlt.P.Fr5.freeOf2_of_four_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:55.094618+00:00
-- url     : https://prove2.me/theorems/8880106a-a152-4ce1-a11c-afe5e9b2bf02
-- title:
--   Fr5: free Of2 of four entries
-- statement:
--   The Fr5 construction uses the free Of2 of four entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L142-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L142-L145

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
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Fr5.freeOf2_of_four_entries {a : S} {x y z w : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) (hz : FreeOf a z)
    (hw : FreeOf a w) : FreeOf2 a !![x, y; z, w] := by sorry
