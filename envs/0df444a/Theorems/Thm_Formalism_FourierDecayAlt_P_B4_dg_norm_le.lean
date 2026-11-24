-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_norm_le
-- name    : Formalism.FourierDecayAlt.P.B4.dg_norm_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:26:20.928979+00:00
-- url     : https://prove2.me/theorems/c0a17a03-778d-40a8-bb30-aa0ed85bd3f4
-- title:
--   B4: dg norm le
-- statement:
--   The B4 construction uses the dg norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L976-L989
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L976-L989

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

theorem Formalism.FourierDecayAlt.P.B4.dg_norm_le {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) (i : Fin (2 * r + k + 1)) :
    ‖dg k r t i‖ ≤ 2 ^ r := by sorry
