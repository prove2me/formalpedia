-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_const_mt
-- name    : Formalism.FourierDecayAlt.P.S3dx4.meas_const_mt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:33.505091+00:00
-- url     : https://prove2.me/theorems/f3f6d73e-1c67-5e88-b8fb-278d8cbfd6ce
-- title:
--   S3dx4: meas const mt
-- statement:
--   The S3dx4 construction uses the meas const mt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L74-L75

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableEnormComposition
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

theorem Formalism.FourierDecayAlt.P.S3dx4.meas_const_mt (c : Formalism.QuantumDeterminants.Mt k r) {α : Type*} [MeasurableSpace α] :
    Measurable (fun _ : α => c) := by sorry
