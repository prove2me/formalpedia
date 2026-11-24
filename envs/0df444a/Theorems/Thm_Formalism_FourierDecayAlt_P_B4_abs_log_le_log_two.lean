-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_abs_log_le_log_two
-- name    : Formalism.FourierDecayAlt.P.B4.abs_log_le_log_two
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:30:27.339392+00:00
-- url     : https://prove2.me/theorems/25a7e522-be7f-4cc0-98e5-ecde588f05fc
-- title:
--   B4: abs log le log two
-- statement:
--   The B4 construction uses the abs log le log two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1274-L1282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1274-L1282

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

theorem Formalism.FourierDecayAlt.P.B4.abs_log_le_log_two {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : |Real.log t| ≤ Real.log 2 := by sorry
