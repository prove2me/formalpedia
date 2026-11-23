-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_T_Tstar
-- name    : Formalism.FourierDecayAlt.P.Wd7.comm_T_Tstar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:14.0108+00:00
-- url     : https://prove2.me/theorems/36d18279-c155-4e80-a3b4-e1333c508bb3
-- title:
--   Wd7: comm T Tstar
-- statement:
--   The Wd7 construction uses the comm T Tstar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L478-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L478-L482

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

theorem Formalism.FourierDecayAlt.P.Wd7.comm_T_Tstar (σ : Site A) (hσ : IsSite σ) (Y Y' : K) (i j k l : Fin 2) :
    Commute (Ts σ Y i j) (star (Ts σ Y' k l)) := by sorry
