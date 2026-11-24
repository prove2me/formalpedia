-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_gN_diag
-- name    : Formalism.FourierDecayAlt.P.B4.gN_diag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:55.634997+00:00
-- url     : https://prove2.me/theorems/15c19fef-1ba1-4830-8592-c4675392ebdb
-- title:
--   B4: g N diag
-- statement:
--   The B4 construction uses the g N diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1074-L1100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1074-L1100

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

theorem Formalism.FourierDecayAlt.P.B4.gN_diag (d₁ d₂ : Fin (2 * r + k + 1) → ℂ) (κ : ℝ) (h₁ : ∀ i, ‖d₁ i‖ ≤ κ)
    (h₂ : ∀ i, ‖d₂ i‖ ≤ κ) (g : Mat k r) :
    gN (Matrix.diagonal d₁ * g * Matrix.diagonal d₂) ≤ κ ^ 2 * gN g := by sorry
