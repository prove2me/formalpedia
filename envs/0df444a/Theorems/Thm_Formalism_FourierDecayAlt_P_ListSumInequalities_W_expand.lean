-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_W_expand
-- name    : Formalism.FourierDecayAlt.P.ListSumInequalities.W_expand
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:48:48.144503+00:00
-- url     : https://prove2.me/theorems/56269420-3340-42ba-800d-a4fc45e11573
-- title:
--   List Sum Inequalities: W expand
-- statement:
--   The List Sum Inequalities construction uses the W expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L184-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L184-L255

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

theorem Formalism.FourierDecayAlt.P.ListSumInequalities.W_expand : ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ F : Mat k r → E,
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) F → ∀ g ∈ GV k r,
      W w F g = ((expW w).map fun p => p.1 • W p.2 F g).sum := by sorry
