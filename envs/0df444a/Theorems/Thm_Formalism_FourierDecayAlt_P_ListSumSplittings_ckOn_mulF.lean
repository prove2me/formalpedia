-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_mulF
-- name    : Formalism.FourierDecayAlt.P.ListSumSplittings.ckOn_mulF
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:07:46.635221+00:00
-- url     : https://prove2.me/theorems/e98f3986-9217-4aa3-aa15-60b486dafce0
-- title:
--   List Sum Splittings: ck On mul F
-- statement:
--   The List Sum Splittings construction uses the ck On mul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L43-L52

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

theorem Formalism.FourierDecayAlt.P.ListSumSplittings.ckOn_mulF {f : Mat k r → ℂ} {H : Mat k r → E} {m : ℕ∞} (hf : CkOn m (GV k r) f)
    (hH : CkOn m (GV k r) H) : CkOn m (GV k r) (fun g => f g • H g) := by sorry
