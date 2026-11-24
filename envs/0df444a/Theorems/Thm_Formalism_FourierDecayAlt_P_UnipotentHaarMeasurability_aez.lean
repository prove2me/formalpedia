-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_aez
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.aez
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:29:04.270253+00:00
-- url     : https://prove2.me/theorems/891c5977-9903-4aab-bfa6-9b695a1e86bd
-- title:
--   Unipotent Haar Measurability: aez
-- statement:
--   The Unipotent Haar Measurability construction uses the aez property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroOfAe.lean#L116-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroOfAe.lean#L116-L199

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

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.aez {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : MX → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hμN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hμG : PI.BesselPeriodGGP.IsHaarOn UHk μG)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) νq)
    (F : MX → Wp) (hFc : ContinuousOn F UHk)
    (hFeq : ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ UHk,
      F (h * n * g) = Formalism.QuantumDeterminants.psi k r z c n • π h (F g))
    (hl2 : PI.BesselPeriodGGP.l2SG νq F = 0) : ∀ g ∈ UHk, F g = 0 := by sorry
