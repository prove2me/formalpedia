-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieBracketMultiplication_op_hasDeriv
-- name    : Formalism.FourierDecayAlt.P.LieBracketMultiplication.op_hasDeriv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:39.065874+00:00
-- url     : https://prove2.me/theorems/da3f37a7-56eb-53ca-87aa-1c27e2065dd8
-- title:
--   Lie Bracket Multiplication: op has Deriv
-- statement:
--   The Lie Bracket Multiplication construction uses the op has Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L262-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L262-L270

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieBracketMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LieBracketMultiplication
variable {k r : ℕ}
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem Formalism.FourierDecayAlt.P.LieBracketMultiplication.op_hasDeriv (A B : W →L[ℂ] W) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) * B * NormedSpace.exp (s • (-A))) (A * B - B * A) 0 := by sorry
