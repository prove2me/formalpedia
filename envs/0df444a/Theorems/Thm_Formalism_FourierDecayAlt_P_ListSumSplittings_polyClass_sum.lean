-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_sum
-- name    : Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:08:34.776261+00:00
-- url     : https://prove2.me/theorems/de093b76-fda9-4170-925a-a0c5aa1d252b
-- title:
--   List Sum Splittings: poly Class sum
-- statement:
--   The List Sum Splittings construction uses the poly Class sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L226-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L226-L236

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

theorem Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_sum {ι : Type*} (s : Finset ι) (D : ℕ) (P : ι → Mat k r → ℂ)
    (h : ∀ i ∈ s, PolyClass D (P i)) : PolyClass D (fun g => ∑ i ∈ s, P i g) := by sorry
