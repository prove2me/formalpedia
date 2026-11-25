-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SkewHermitianParts_lie_inWb
-- name    : Formalism.FourierDecayAlt.P.SkewHermitianParts.lie_inWb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:10:20.357602+00:00
-- url     : https://prove2.me/theorems/626a77cd-3fda-54fe-8887-5d8b4f03fee1
-- title:
--   Skew Hermitian Parts: lie in Wb
-- statement:
--   The Skew Hermitian Parts construction uses the lie in Wb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L68-L75

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.SkewHermitianParts
open AnisotropicColumnSums
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.SkewHermitianParts.lie_inWb {X : Mx k r} (hX : inLieLev k r (Fin.last r) X) (v : Fin (2 * r + k + 1) → ℂ) :
    inWb k r (X *ᵥ v) := by sorry
