-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_gN_dil
-- name    : Formalism.FourierDecayAlt.P.B4.gN_dil
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:28:41.127095+00:00
-- url     : https://prove2.me/theorems/80409759-cd3c-4c48-a1f0-8904eadd0d71
-- title:
--   B4: g N dil
-- statement:
--   The B4 construction uses the g N dil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1102-L1121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1102-L1121

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.B4.gN_dil {τ₁ τ₂ A : ℝ} (h₁ : τ₁ ∈ Set.Icc (1 / 2 : ℝ) 2) (h₂ : τ₂ ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hA : 0 ≤ A) (g : Mat k r) :
    gN g ^ A ≤ ((4 : ℝ) ^ r) ^ A * gN (aDil k r τ₁ * g * aDil k r τ₂) ^ A := by sorry
