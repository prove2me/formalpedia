-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_mt_cont
-- name    : Formalism.FourierDecayAlt.P.S3dx4.mt_cont
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:12:54.55638+00:00
-- url     : https://prove2.me/theorems/c9103b47-e257-4b29-8ea5-50b434f41ec3
-- title:
--   S3dx4: mt cont
-- statement:
--   The S3dx4 construction uses the mt cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InnerBound.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InnerBound.lean#L32-L36

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNMulRpow
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
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

theorem Formalism.FourierDecayAlt.P.S3dx4.mt_cont : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := by sorry
