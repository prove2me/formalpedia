-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_mul
-- name    : Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:07:25.696082+00:00
-- url     : https://prove2.me/theorems/aa1c59b2-7fc6-4739-acd2-b375bdb18751
-- title:
--   List Sum Splittings: poly Class mul
-- statement:
--   The List Sum Splittings construction uses the poly Class mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L166-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L166-L196

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

theorem Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_mul {D1 D2 : ℕ} {P Q : Mat k r → ℂ} (hP : PolyClass D1 P) (hQ : PolyClass D2 Q) :
    PolyClass (D1 + D2) (fun g => P g * Q g) := by sorry
