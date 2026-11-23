-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_mul
-- name    : Formalism.FourierDecayAlt.P.Wd7.free_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:10.919803+00:00
-- url     : https://prove2.me/theorems/27ea465a-0d42-4042-808a-f7903dc4fd3b
-- title:
--   Wd7: free mul
-- statement:
--   The Wd7 construction uses the free mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L177-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L177-L178

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd7.free_mul {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x * y) := by sorry
