-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_measurable_enorm_composition
-- name    : Formalism.FourierDecayAlt.P.S3dx4.measurable_enorm_composition
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:41:06.722942+00:00
-- url     : https://prove2.me/theorems/b10d760a-d2af-42b6-92c0-5b1855991dbe
-- title:
--   S3dx4: measurable enorm composition
-- statement:
--   The S3dx4 construction uses the measurable enorm composition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L29-L31

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

theorem Formalism.FourierDecayAlt.P.S3dx4.measurable_enorm_composition {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) : Measurable (fun t => ‖e0 (Matrix.of (f t))‖ₑ) := by sorry
