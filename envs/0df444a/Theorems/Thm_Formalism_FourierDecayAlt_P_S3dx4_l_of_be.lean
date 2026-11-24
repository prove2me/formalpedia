-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_l_of_be
-- name    : Formalism.FourierDecayAlt.P.S3dx4.l_of_be
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:09:05.147794+00:00
-- url     : https://prove2.me/theorems/21576ce0-dfca-4c28-9f54-feb06b834c9e
-- title:
--   S3dx4: l of be
-- statement:
--   The S3dx4 construction uses the l of be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMemMeasurableSet.lean#L79-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMemMeasurableSet.lean#L79-L91

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbConvDDOfDecDD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMemMeasurableSet
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

theorem Formalism.FourierDecayAlt.P.S3dx4.l_of_be {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {σ : Mx k r → (H →L[ℂ] H)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {l : H → Wp} {x v : H}
    (hbe : be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x)) (hlv : l v ≠ 0) :
    l x = ((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹ • (be z c π σ μW μN x v) (l v) := by sorry
