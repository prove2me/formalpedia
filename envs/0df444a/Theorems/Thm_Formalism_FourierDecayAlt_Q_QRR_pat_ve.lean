-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_ve
-- name    : Formalism.FourierDecayAlt.Q.QRR.pat_ve
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:47:01.054397+00:00
-- url     : https://prove2.me/theorems/f74d33ab-37c2-44d2-a204-765edaca7d54
-- title:
--   QRR: pat ve
-- statement:
--   The QRR construction uses the pat ve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L255-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L255-L261

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

theorem Formalism.FourierDecayAlt.Q.QRR.pat_ve (l : Fin r) (j : Fin (mdim k r l.succ)) :
    Pat k r l (Matrix.single (posL k r l.succ j) (esI k r l) 1) := by sorry
