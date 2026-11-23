-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_smul
-- name    : Formalism.FourierDecayAlt.P.Wd7.free_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:03.422714+00:00
-- url     : https://prove2.me/theorems/c260a639-9199-40e0-be9d-93264cda7ac9
-- title:
--   Wd7: free smul
-- statement:
--   The Wd7 construction uses the free smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L186-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L186-L187

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

theorem Formalism.FourierDecayAlt.P.Wd7.free_smul {K : Type} [Field K] [Algebra K A] {a : S} (k : K) {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) :
    FreeOf a (k • x) := by sorry
