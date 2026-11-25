-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieBracketMultiplication_lie_bracket
-- name    : Formalism.FourierDecayAlt.P.LieBracketMultiplication.lie_bracket
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:32.076676+00:00
-- url     : https://prove2.me/theorems/24b90cbd-6d93-5793-8f20-c1a259bc9341
-- title:
--   Lie Bracket Multiplication: lie bracket
-- statement:
--   The Lie Bracket Multiplication construction uses the lie bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L87-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L87-L107

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
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem Formalism.FourierDecayAlt.P.LieBracketMultiplication.lie_bracket {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) :
    InLieW k r z (X * Y - Y * X) := by sorry
