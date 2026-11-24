-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_op_expand
-- name    : Formalism.FourierDecayAlt.P.ListSumInequalities.op_expand
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:48:57.032226+00:00
-- url     : https://prove2.me/theorems/c029e641-3e90-4003-826c-7f2d2a2c9249
-- title:
--   List Sum Inequalities: op expand
-- statement:
--   The List Sum Inequalities construction uses the op expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L86-L97

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

theorem Formalism.FourierDecayAlt.P.ListSumInequalities.op_expand {H : Mat k r → E} {X g : Mat k r} (b : Bool) (hX : inLie k r X)
    (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) (hg : g ∈ GV k r) :
    op b X H g = ∑ i, kc i X • op b (Lt i) H g := by sorry
