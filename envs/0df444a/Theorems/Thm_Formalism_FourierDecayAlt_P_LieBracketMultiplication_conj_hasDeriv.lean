-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieBracketMultiplication_conj_hasDeriv
-- name    : Formalism.FourierDecayAlt.P.LieBracketMultiplication.conj_hasDeriv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:27:50.614873+00:00
-- url     : https://prove2.me/theorems/72b16977-be6c-53c2-a170-f5358db16122
-- title:
--   Lie Bracket Multiplication: conj has Deriv
-- statement:
--   The Lie Bracket Multiplication construction uses the conj has Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L245-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L245-L258

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

theorem Formalism.FourierDecayAlt.P.LieBracketMultiplication.conj_hasDeriv (X Y : Mx k r) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X)))
      (X * Y - Y * X) 0 := by sorry
