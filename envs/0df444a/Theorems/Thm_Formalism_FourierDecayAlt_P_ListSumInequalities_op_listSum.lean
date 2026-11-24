-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_op_listSum
-- name    : Formalism.FourierDecayAlt.P.ListSumInequalities.op_listSum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:51:45.743943+00:00
-- url     : https://prove2.me/theorems/2f0ed5a6-636f-49ce-9d03-eae7e6143735
-- title:
--   List Sum Inequalities: op list Sum
-- statement:
--   The List Sum Inequalities construction uses the op list Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L61-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L61-L80

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

theorem Formalism.FourierDecayAlt.P.ListSumInequalities.op_listSum {b : Bool} {X : Mat k r} (hX : inLie k r X) :
    ∀ (L : List (ℝ × (Mat k r → E))), (∀ p ∈ L, CkOn ((1 : ℕ) : ℕ∞) (GV k r) p.2) →
      ∀ g ∈ GV k r, op b X (fun g' => (L.map fun p => p.1 • p.2 g').sum) g =
        (L.map fun p => p.1 • op b X p.2 g).sum := by sorry
