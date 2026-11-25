-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SkewHermitianParts_inLie_zero
-- name    : Formalism.FourierDecayAlt.P.SkewHermitianParts.inLie_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:04.757521+00:00
-- url     : https://prove2.me/theorems/6cc0a2c7-135f-5535-b53f-f91811f7db30
-- title:
--   Skew Hermitian Parts: in Lie zero
-- statement:
--   The Skew Hermitian Parts construction uses the in Lie zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L200-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L200-L201

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

theorem Formalism.FourierDecayAlt.P.SkewHermitianParts.inLie_zero (z : Fin (2 * r + k + 1) → ℂ) : InLieW k r z 0 := by sorry
