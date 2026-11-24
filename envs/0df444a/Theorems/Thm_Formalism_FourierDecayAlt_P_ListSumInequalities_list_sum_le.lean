-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_le
-- name    : Formalism.FourierDecayAlt.P.ListSumInequalities.list_sum_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:49:41.555802+00:00
-- url     : https://prove2.me/theorems/6d8060c1-0f9a-421b-b658-e8ca30cbd6bb
-- title:
--   List Sum Inequalities: list sum le
-- statement:
--   The List Sum Inequalities construction uses the list sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L30-L36

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.ListSumInequalities.list_sum_le {α : Type*} (L : List α) (f f' : α → ℝ) (h : ∀ a ∈ L, f a ≤ f' a) :
    (L.map f).sum ≤ (L.map f').sum := by sorry
