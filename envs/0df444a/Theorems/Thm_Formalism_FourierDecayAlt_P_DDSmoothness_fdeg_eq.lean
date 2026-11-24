-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_fdeg_eq
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:11:00.064899+00:00
-- url     : https://prove2.me/theorems/f033955a-227e-46b7-857a-80e908d80e68
-- title:
--   DDSmoothness: fdeg eq
-- statement:
--   The DDSmoothness construction uses the fdeg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMeasurableSet.lean#L131-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMeasurableSet.lean#L131-L158

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq {σ : Mx k r → (H →L[ℂ] H)} {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} {d : ℝ} (hd : 0 < d)
    (hS : ∀ v w v' w' : H,
      Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {u : H} (hu : u ≠ 0) : PI.BesselPeriodGGP.fdegH μG σ u = d := by sorry
