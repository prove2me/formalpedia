-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_sum_fun_succ
-- name    : Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.sum_fun_succ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:44:55.036059+00:00
-- url     : https://prove2.me/theorems/ea52609c-a46d-4786-bdb5-e26ff14904ba
-- title:
--   Finite Sum Local Expansion: sum fun succ
-- statement:
--   The Finite Sum Local Expansion construction uses the sum fun succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L134-L138

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_PI_QnCovHat2W_sum_fun_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.sum_fun_succ {α M : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid M] {t : ℕ}
    (G : (Fin (t + 1) → α) → M) :
    ∑ C : Fin (t + 1) → α, G C = ∑ a : α, ∑ c : Fin t → α, G (Fin.cons a c) := by sorry
