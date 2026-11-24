-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_op_listSumF
-- name    : Formalism.FourierDecayAlt.P.ListSumSplittings.op_listSumF
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:08:22.659923+00:00
-- url     : https://prove2.me/theorems/01efc1bc-7977-49ab-a208-035cb39e434b
-- title:
--   List Sum Splittings: op list Sum F
-- statement:
--   The List Sum Splittings construction uses the op list Sum F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L79-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L79-L91

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

theorem Formalism.FourierDecayAlt.P.ListSumSplittings.op_listSumF {α : Type*} {b : Bool} {X : Mat k r} (hX : inLie k r X) (φ : α → Mat k r → E) :
    ∀ (L : List α), (∀ a ∈ L, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (φ a)) →
      ∀ g ∈ GV k r, op b X (fun g' => (L.map fun a => φ a g').sum) g = (L.map fun a => op b X (φ a) g).sum := by sorry
