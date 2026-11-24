-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_listSumF
-- name    : Formalism.FourierDecayAlt.P.ListSumSplittings.ckOn_listSumF
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:09:40.932427+00:00
-- url     : https://prove2.me/theorems/af329bd6-9eb5-4018-8eae-b876ff68ac4a
-- title:
--   List Sum Splittings: ck On list Sum F
-- statement:
--   The List Sum Splittings construction uses the ck On list Sum F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L66-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L66-L77

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

theorem Formalism.FourierDecayAlt.P.ListSumSplittings.ckOn_listSumF {α : Type*} (φ : α → Mat k r → E) {m : ℕ∞} :
    ∀ (L : List α), (∀ a ∈ L, CkOn m (GV k r) (φ a)) →
      CkOn m (GV k r) (fun g => (L.map fun a => φ a g).sum) := by sorry
