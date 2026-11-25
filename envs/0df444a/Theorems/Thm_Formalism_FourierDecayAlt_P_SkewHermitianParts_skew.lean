-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SkewHermitianParts_skew
-- name    : Formalism.FourierDecayAlt.P.SkewHermitianParts.skew
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:40:02.296429+00:00
-- url     : https://prove2.me/theorems/9e702674-b2d0-4525-a33c-a621e64c6d3f
-- title:
--   Skew Hermitian Parts: skew
-- statement:
--   The Skew Hermitian Parts construction uses the skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L61-L66

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

theorem Formalism.FourierDecayAlt.P.SkewHermitianParts.skew {X : Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (X *ᵥ v) w = -herm (Hpk k r) v (X *ᵥ w) := by sorry
