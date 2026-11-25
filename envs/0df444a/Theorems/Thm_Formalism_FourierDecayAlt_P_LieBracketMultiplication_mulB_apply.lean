-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieBracketMultiplication_mulB_apply
-- name    : Formalism.FourierDecayAlt.P.LieBracketMultiplication.mulB_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:20.384412+00:00
-- url     : https://prove2.me/theorems/83577798-dd81-574f-8c92-1a7c4b9bbcac
-- title:
--   Lie Bracket Multiplication: mul B apply
-- statement:
--   The Lie Bracket Multiplication construction uses the mul B apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L243-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L243-L243

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

theorem Formalism.FourierDecayAlt.P.LieBracketMultiplication.mulB_apply (X Y : Mx k r) : mulB k r X Y = X * Y := by sorry
