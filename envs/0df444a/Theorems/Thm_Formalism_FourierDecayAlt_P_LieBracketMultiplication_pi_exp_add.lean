-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieBracketMultiplication_pi_exp_add
-- name    : Formalism.FourierDecayAlt.P.LieBracketMultiplication.pi_exp_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:18:35.118634+00:00
-- url     : https://prove2.me/theorems/93b20144-9640-4d95-95a0-543447ad6b2d
-- title:
--   Lie Bracket Multiplication: pi exp add
-- statement:
--   The Lie Bracket Multiplication construction uses the pi exp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L179-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L179-L198

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
variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem Formalism.FourierDecayAlt.P.LieBracketMultiplication.pi_exp_add (hT : Qr.Trotter) (hM : Qr.TrotterMx) (hP : Qr.PiExp) (hπ : Qr.IsRepW k r z π) {X Y : Mx k r}
    (hX : InLieW k r z X) (hY : InLieW k r z Y) (t : ℝ) :
    π (NormedSpace.exp ((t : ℂ) • (X + Y))) = NormedSpace.exp (t • (dOp π X + dOp π Y)) := by sorry
