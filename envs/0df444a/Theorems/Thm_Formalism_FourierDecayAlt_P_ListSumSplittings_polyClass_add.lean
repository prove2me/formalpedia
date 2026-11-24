-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_add
-- name    : Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:09:54.271058+00:00
-- url     : https://prove2.me/theorems/ebc8cb1a-a7e3-4e18-baac-c95260a8f6aa
-- title:
--   List Sum Splittings: poly Class add
-- statement:
--   The List Sum Splittings construction uses the poly Class add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L154-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L154-L164

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

theorem Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_add {D : ℕ} {P Q : Mat k r → ℂ} (hP : PolyClass D P) (hQ : PolyClass D Q) :
    PolyClass D (fun g => P g + Q g) := by sorry
