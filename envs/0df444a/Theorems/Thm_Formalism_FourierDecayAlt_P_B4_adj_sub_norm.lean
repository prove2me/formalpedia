-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_sub_norm
-- name    : Formalism.FourierDecayAlt.P.B4.adj_sub_norm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:30:02.722872+00:00
-- url     : https://prove2.me/theorems/34033463-58e9-4c62-80cb-50a28be36c8f
-- title:
--   B4: adj sub norm
-- statement:
--   The B4 construction uses the adj sub norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1044-L1072
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1044-L1072

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

theorem Formalism.FourierDecayAlt.P.B4.adj_sub_norm {τ : ℝ} (hτ : τ ∈ Set.Icc (1 / 2 : ℝ) 2) (X : Mat k r) :
    ‖(aDil k r τ)⁻¹ * X * aDil k r τ - X‖ ≤ 8 * 4 ^ r * |τ - 1| * ‖X‖ := by sorry
