-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_VMonicMonicShiftEvaluation_term
-- name    : Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.term
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:31.298927+00:00
-- url     : https://prove2.me/theorems/25693f62-b487-4254-a369-f673a6151035
-- title:
--   VMonic Monic Shift Evaluation: term
-- statement:
--   The VMonic Monic Shift Evaluation construction uses the term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonicShiftEvaluation/CapelliPolynomialMonic.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonicShiftEvaluation/CapelliPolynomialMonic.lean#L40-L43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_EvalXAddCMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_CapelliPolynomialMonic
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

theorem Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.term (r : ℕ) (c : R r E) (Y : ℂ) (j : ℕ) (f : WSm r E) :
    (((c * algebraMap ℂ (R r E) Y ^ j) f : WSm r E) : (Fin r → ℂ) → E) =
      Y ^ j • ((c f : WSm r E) : (Fin r → ℂ) → E) := by sorry
