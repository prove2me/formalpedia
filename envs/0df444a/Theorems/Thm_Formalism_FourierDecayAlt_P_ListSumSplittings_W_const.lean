-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_W_const
-- name    : Formalism.FourierDecayAlt.P.ListSumSplittings.W_const
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:09:58.568713+00:00
-- url     : https://prove2.me/theorems/4c548703-f4c7-4eac-9b12-befec0516140
-- title:
--   List Sum Splittings: W const
-- statement:
--   The List Sum Splittings construction uses the W const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L139-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L139-L147

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.ListSumSplittings.W_const (c : ℂ) : ∀ a : List (Bool × Mat k r), ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ W a (fun _ => c) = fun _ => c' := by sorry
