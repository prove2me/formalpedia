-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_cw_mat
-- name    : Formalism.FourierDecayAlt.P.Wd8.cw_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:49.684694+00:00
-- url     : https://prove2.me/theorems/3592f7bc-f2c7-42ce-adf3-b677a423465e
-- title:
--   Wd8: cw mat
-- statement:
--   The Wd8 construction uses the cw mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L372-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L372-L381

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd8.cw_mat (X X' Q V VH U : M2 (SlopeTestRemainingChoices S A)) (hA : X' * V * U = U * V * X')
    (hB : VH * X * U = U * X * VH) (hQ : Commute Q U) :
    VH * (X * Q * X') * V * U = U * X * (VH * Q * V) * X' := by sorry
