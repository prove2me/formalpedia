-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_TTw_corner
-- name    : Formalism.FourierDecayAlt.P.Wd7.TTw_corner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:13.301216+00:00
-- url     : https://prove2.me/theorems/be6afd5e-11bc-4da1-8306-cc26ea079acb
-- title:
--   Wd7: TTw corner
-- statement:
--   The Wd7 construction uses the TTw corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L369-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L369-L374

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

theorem Formalism.FourierDecayAlt.P.Wd7.TTw_corner (QQ : K → M2 A) (w : List (Letter K S)) (Y : K)
    (hn : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hr : Reg w Y) (z : Ix S) :
    (TTw QQ w Y 0 0) z e1 = if z = e1 then QQ Y 0 0 else 0 := by sorry
