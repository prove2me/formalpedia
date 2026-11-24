-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_TTw_transpose
-- name    : Formalism.FourierDecayAlt.P.Wd7.TTw_transpose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:22.436945+00:00
-- url     : https://prove2.me/theorems/a343ab34-4478-4ba5-b39f-253d689b2fbc
-- title:
--   Wd7: TTw transpose
-- statement:
--   The Wd7 construction uses the TTw transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L561-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L561-L617

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
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd7.TTw_transpose (QQ : K → M2 A) (w : List (Letter K S)) (hn : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup)
    (Y : K) : (TTw QQ w Y)ᵀ = (Xp w Y)ᵀ * lift0 (QQ Y)ᵀ * (Xm w Y)ᵀ := by sorry
