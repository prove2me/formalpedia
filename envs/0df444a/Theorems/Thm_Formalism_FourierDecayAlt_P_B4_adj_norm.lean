-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_norm
-- name    : Formalism.FourierDecayAlt.P.B4.adj_norm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:30:16.019835+00:00
-- url     : https://prove2.me/theorems/6ef7549d-dd6d-4fa7-b8b5-38d31588e0fc
-- title:
--   B4: adj norm
-- statement:
--   The B4 construction uses the adj norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1032-L1042
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1032-L1042

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

theorem Formalism.FourierDecayAlt.P.B4.adj_norm {τ : ℝ} (hτ : τ ∈ Set.Icc (1 / 2 : ℝ) 2) (X : Mat k r) :
    ‖(aDil k r τ)⁻¹ * X * aDil k r τ‖ ≤ 4 ^ r * ‖X‖ := by sorry
