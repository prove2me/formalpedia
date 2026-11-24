-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_bessel_smul
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:12:53.152538+00:00
-- url     : https://prove2.me/theorems/24337270-8b1d-4fc3-be05-a34624f247b4
-- title:
--   DDSmoothness: bessel smul
-- statement:
--   The DDSmoothness construction uses the bessel smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMeasurableSet.lean#L167-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMeasurableSet.lean#L167-L179

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

theorem Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {σ : Mx k r → (H →L[ℂ] H)}
    {π : Mx k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B) (κ : ℂ) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun x => κ • B x) := by sorry
