-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_flatMap
-- name    : Formalism.FourierDecayAlt.P.ListSumInequalities.list_sum_flatMap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:49:06.087797+00:00
-- url     : https://prove2.me/theorems/eb2c4b01-36ee-45f3-90e6-56ca1cdd5c71
-- title:
--   List Sum Inequalities: list sum flat Map
-- statement:
--   The List Sum Inequalities construction uses the list sum flat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L16-L20

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

theorem Formalism.FourierDecayAlt.P.ListSumInequalities.list_sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (h : β → M) :
    ((L.flatMap f).map h).sum = (L.map fun a => ((f a).map h).sum).sum := by sorry
