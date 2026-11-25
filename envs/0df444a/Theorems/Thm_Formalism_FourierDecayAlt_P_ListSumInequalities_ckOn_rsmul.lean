-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_ckOn_rsmul
-- name    : Formalism.FourierDecayAlt.P.ListSumInequalities.ckOn_rsmul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:27:40.518707+00:00
-- url     : https://prove2.me/theorems/6b50ff0e-7dab-40c7-a4c2-8e56840ba2e0
-- title:
--   List Sum Inequalities: ck On rsmul
-- statement:
--   The List Sum Inequalities construction uses the ck On rsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean#L49-L55

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

theorem Formalism.FourierDecayAlt.P.ListSumInequalities.ckOn_rsmul {f : Mat k r → E} {m : ℕ∞} (a : ℝ) (hf : CkOn m (GV k r) f) :
    CkOn m (GV k r) (fun g => a • f g) := by sorry
