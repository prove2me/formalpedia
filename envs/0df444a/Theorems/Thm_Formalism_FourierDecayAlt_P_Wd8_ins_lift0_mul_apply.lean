-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_ins_lift0_mul_apply
-- name    : Formalism.FourierDecayAlt.P.Wd8.ins_lift0_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:47:17.832231+00:00
-- url     : https://prove2.me/theorems/f29c5704-244e-4988-896b-fa3993485141
-- title:
--   Wd8: ins lift0 mul apply
-- statement:
--   The Wd8 construction uses the ins lift0 mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L456-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L456-L462

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

theorem Formalism.FourierDecayAlt.P.Wd8.ins_lift0_mul_apply (a : S) (M : M2 A) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((ins a (lift0 M) : SlopeTestRemainingChoices S A) * B) x y = ∑ j, M (x a) j * B (Function.update x a j) y := by sorry
