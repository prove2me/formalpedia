-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_eU_apply
-- name    : Formalism.FourierDecayAlt.P.Wd7.mul_eU_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:05.169442+00:00
-- url     : https://prove2.me/theorems/661829d7-c6ab-45e2-b082-fda00d347bf2
-- title:
--   Wd7: mul e U apply
-- statement:
--   The Wd7 construction uses the mul e U apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L60-L66

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

theorem Formalism.FourierDecayAlt.P.Wd7.mul_eU_apply (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    (B * (eU a i j : SlopeTestRemainingChoices S A)) x y = if y a = j then B x (Function.update y a i) else 0 := by sorry
