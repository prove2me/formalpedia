-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_hn
-- name    : Formalism.FourierDecayAlt.P.S3dx4.meas_hn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:35:26.52066+00:00
-- url     : https://prove2.me/theorems/9f92b95a-0e47-51c8-8a46-3588d781305b
-- title:
--   S3dx4: meas hn
-- statement:
--   The S3dx4 construction uses the meas hn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L33-L36

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

theorem Formalism.FourierDecayAlt.P.S3dx4.meas_hn {α : Type*} [MeasurableSpace α] {f : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hf : Measurable f) :
    Measurable (fun t => (fun i j => (Matrix.of (f t).1 * Matrix.of (f t).2) i j : Formalism.QuantumDeterminants.Mt k r)) := by sorry
