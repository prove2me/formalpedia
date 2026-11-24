-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_zero_of_ae
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.zero_of_ae
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:28:53.908214+00:00
-- url     : https://prove2.me/theorems/b0dfe73f-1513-457a-a4ca-728f46d51d22
-- title:
--   Unipotent Haar Measurability: zero of ae
-- statement:
--   The Unipotent Haar Measurability construction uses the zero of ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroOfAe.lean#L40-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroOfAe.lean#L40-L114

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

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.zero_of_ae {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : PI.BesselPeriodGGP.IsHaarOn UHk μG)
    {E : Type*} [NormedAddCommGroup E] {f : MX → E} (hf : ContinuousOn f UHk)
    (hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UHk → f (Matrix.of x) = 0)
    {g0 : MX} (hg0 : g0 ∈ UHk) : f g0 = 0 := by sorry
