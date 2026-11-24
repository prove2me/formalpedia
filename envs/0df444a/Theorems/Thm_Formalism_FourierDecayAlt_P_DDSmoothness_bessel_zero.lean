-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_bessel_zero
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.bessel_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:10:29.370185+00:00
-- url     : https://prove2.me/theorems/415fb0aa-9437-4aac-8123-15c1bc1a6f89
-- title:
--   DDSmoothness: bessel zero
-- statement:
--   The DDSmoothness construction uses the bessel zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMeasurableSet.lean#L181-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMeasurableSet.lean#L181-L185

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
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem Formalism.FourierDecayAlt.P.DDSmoothness.bessel_zero {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {σ : Mx k r → (H →L[ℂ] H)}
    {π : Mx k r → (Wp →L[ℂ] Wp)} :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun _ => (0 : Wp)) := by sorry
