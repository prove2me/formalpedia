-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_vf_sum
-- name    : Formalism.FourierDecayAlt.P.ListSumInequalities.vf_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:33.534478+00:00
-- url     : https://prove2.me/theorems/a98ba4ab-35db-4089-b860-c19f41fcd020
-- title:
--   List Sum Inequalities: vf sum
-- statement:
--   The List Sum Inequalities construction uses the vf sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L82-L84

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

theorem Formalism.FourierDecayAlt.P.ListSumInequalities.vf_sum (b : Bool) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Y : ι → Mat k r) (g : Mat k r) :
    vf b (∑ i ∈ s, c i • Y i) g = ∑ i ∈ s, c i • vf b (Y i) g := by sorry
