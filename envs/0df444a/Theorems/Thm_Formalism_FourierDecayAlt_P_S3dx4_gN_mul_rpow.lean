-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_gN_mul_rpow
-- name    : Formalism.FourierDecayAlt.P.S3dx4.gN_mul_rpow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:39.112834+00:00
-- url     : https://prove2.me/theorems/44ad4579-aa84-44db-b4f3-35989bf38092
-- title:
--   S3dx4: g N mul rpow
-- statement:
--   The S3dx4 construction uses the g N mul rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GNMulRpow.lean#L52-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GNMulRpow.lean#L52-L73

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

theorem Formalism.FourierDecayAlt.P.S3dx4.gN_mul_rpow (hNI : NormInv) {x Y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hY : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ} (hb : 0 ≤ b) :
    B.gN (Y * x) ^ (-b) ≤ B.gN x ^ b * B.gN Y ^ (-b) := by sorry
