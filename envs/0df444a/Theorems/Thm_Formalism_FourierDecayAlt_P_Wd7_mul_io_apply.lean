-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_io_apply
-- name    : Formalism.FourierDecayAlt.P.Wd7.mul_io_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:51.085923+00:00
-- url     : https://prove2.me/theorems/72cc3c17-dc3e-46dc-97d4-0d2ec35f26aa
-- title:
--   Wd7: mul io apply
-- statement:
--   The Wd7 construction uses the mul io apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L149-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L149-L150

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

theorem Formalism.FourierDecayAlt.P.Wd7.mul_io_apply (x : A) (M : SlopeTestRemainingChoices S A) (z y : Ix S) : (M * (io x : SlopeTestRemainingChoices S A)) z y = M z y * x := by sorry
