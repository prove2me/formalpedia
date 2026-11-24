-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_posL_val
-- name    : Formalism.FourierDecayAlt.Q.QRR.posL_val
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:34:33.376984+00:00
-- url     : https://prove2.me/theorems/c49092ce-82d2-4dd0-86d8-1ba21eeb49e1
-- title:
--   QRR: pos L val
-- statement:
--   The QRR construction uses the pos L val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L146-L152

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.QRR.posL_val (l : Fin r) (j : Fin (mdim k r l.succ)) :
    (posL k r l.succ j).val = j.val + (l.val + 1) ∧ j.val + (l.val + 1) < 2 * r + k - l.val := by sorry
