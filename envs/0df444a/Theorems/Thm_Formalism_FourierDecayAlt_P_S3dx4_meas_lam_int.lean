-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_lam_int
-- name    : Formalism.FourierDecayAlt.P.S3dx4.meas_lam_int
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:23:16.422899+00:00
-- url     : https://prove2.me/theorems/8d12b511-3514-4b3b-8f6c-6c7abc53e433
-- title:
--   S3dx4: meas lam int
-- statement:
--   The S3dx4 construction uses the meas lam int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L38-L46

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

theorem Formalism.FourierDecayAlt.P.S3dx4.meas_lam_int {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P Q : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) * γ *
      (Matrix.of (Q t).1 * Matrix.of (Q t).2)⁻¹ * Matrix.of (Y t))‖ₑ) := by sorry
