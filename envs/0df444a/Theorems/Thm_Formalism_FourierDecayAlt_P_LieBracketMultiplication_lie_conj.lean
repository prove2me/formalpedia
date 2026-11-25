-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieBracketMultiplication_lie_conj
-- name    : Formalism.FourierDecayAlt.P.LieBracketMultiplication.lie_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:18:51.229083+00:00
-- url     : https://prove2.me/theorems/16d28eb8-fd84-420c-b931-d4cd735d1e57
-- title:
--   Lie Bracket Multiplication: lie conj
-- statement:
--   The Lie Bracket Multiplication construction uses the lie conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L109-L114

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieBracketMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_lie_conj

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

theorem Formalism.FourierDecayAlt.P.LieBracketMultiplication.lie_conj {X h : Mx k r} (hX : InLieW k r z X) (hh : h ∈ UWset k r z) : InLieW k r z (h * X * h⁻¹) := by sorry
