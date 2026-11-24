-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_matmul
-- name    : Formalism.FourierDecayAlt.P.S3dx4.meas_matmul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:05.833259+00:00
-- url     : https://prove2.me/theorems/8edcefbd-2d6e-4eea-81a8-9a3c2c90f1b5
-- title:
--   S3dx4: meas matmul
-- statement:
--   The S3dx4 construction uses the meas matmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GNMulRpow.lean#L75-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GNMulRpow.lean#L75-L82

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNMulRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.S3dx4.meas_matmul {α : Type*} [MeasurableSpace α] {f g : α → Formalism.QuantumDeterminants.Mt k r}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => (fun i j => (Matrix.of (f p) * Matrix.of (g p)) i j : Formalism.QuantumDeterminants.Mt k r)) := by sorry
