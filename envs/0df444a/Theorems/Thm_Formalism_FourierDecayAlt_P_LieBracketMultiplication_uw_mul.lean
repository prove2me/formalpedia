-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieBracketMultiplication_uw_mul
-- name    : Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:00:37.122057+00:00
-- url     : https://prove2.me/theorems/4dc63bf3-acc8-5288-814c-d9b45920bf74
-- title:
--   Lie Bracket Multiplication: uw mul
-- statement:
--   The Lie Bracket Multiplication construction uses the uw mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L21-L33

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieBracketMultiplication
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_mul

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

theorem Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul {g h : Mx k r} (hg : g ∈ UWset k r z) (hh : h ∈ UWset k r z) : g * h ∈ UWset k r z := by sorry
