-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_VMonicMonicShiftEvaluation_eval_X_add_C_mul
-- name    : Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.eval_X_add_C_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:54:04.030976+00:00
-- url     : https://prove2.me/theorems/0df75cfa-9637-4aa5-a1de-80065897c72e
-- title:
--   VMonic Monic Shift Evaluation: eval X add C mul
-- statement:
--   The VMonic Monic Shift Evaluation construction uses the eval X add C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonicShiftEvaluation/EvalXAddCMul.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonicShiftEvaluation/EvalXAddCMul.lean#L25-L28

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_EvalXAddCMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
open Formalism.QuantumDeterminants
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.eval_X_add_C_mul (r : ℕ) (P : (R r E)[X]) (q : R r E) (Y : ℂ) :
    ((X + C q) * P).eval (algebraMap ℂ (R r E) Y) =
      algebraMap ℂ (R r E) Y * P.eval (algebraMap ℂ (R r E) Y) + q * P.eval (algebraMap ℂ (R r E) Y) := by sorry
