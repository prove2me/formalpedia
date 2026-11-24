-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_apply
-- name    : Formalism.FourierDecayAlt.P.B4.adj_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:27:45.355138+00:00
-- url     : https://prove2.me/theorems/7f2ae70a-3bd1-41b3-addf-23133a186c3d
-- title:
--   B4: adj apply
-- statement:
--   The B4 construction uses the adj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1020-L1022
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1020-L1022

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

theorem Formalism.FourierDecayAlt.P.B4.adj_apply {τ : ℝ} (hτ : τ ≠ 0) (X : Mat k r) (i j : Fin (2 * r + k + 1)) :
    ((aDil k r τ)⁻¹ * X * aDil k r τ) i j = dg k r τ⁻¹ i * X i j * dg k r τ j := by sorry
