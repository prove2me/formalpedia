-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_uh_meas
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.uh_meas
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:29:17.45568+00:00
-- url     : https://prove2.me/theorems/8c450b4f-37dc-47f9-94a0-3861e8c5921b
-- title:
--   Unipotent Haar Measurability: uh meas
-- statement:
--   The Unipotent Haar Measurability construction uses the uh meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroOfAe.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroOfAe.lean#L23-L29

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

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.uh_meas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by sorry
