-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_sigma_one
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.sigma_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:29:07.806796+00:00
-- url     : https://prove2.me/theorems/b3c21a7d-cc59-4422-bc61-9d29abab013d
-- title:
--   Unipotent Haar Measurability: sigma one
-- statement:
--   The Unipotent Haar Measurability construction uses the sigma one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroOfAe.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroOfAe.lean#L31-L38

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroOfAe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
variable {k r : ℕ}
local notation "MX" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
local notation "UHk" => Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.sigma_one {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : MX → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ) : σ 1 = 1 := by sorry
