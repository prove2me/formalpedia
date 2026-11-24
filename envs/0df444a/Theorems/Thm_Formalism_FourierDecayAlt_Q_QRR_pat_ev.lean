-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_ev
-- name    : Formalism.FourierDecayAlt.Q.QRR.pat_ev
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:02:05.381867+00:00
-- url     : https://prove2.me/theorems/b17e58c2-29c9-473b-8baa-60bc285c6f11
-- title:
--   QRR: pat ev
-- statement:
--   The QRR construction uses the pat ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L248-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L248-L253

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

theorem Formalism.FourierDecayAlt.Q.QRR.pat_ev (l : Fin r) (j : Fin (mdim k r l.succ)) :
    Pat k r l (Matrix.single (eI k r l) (posL k r l.succ j) 1) := by sorry
