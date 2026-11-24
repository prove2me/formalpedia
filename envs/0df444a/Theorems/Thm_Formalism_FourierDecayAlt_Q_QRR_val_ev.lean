-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_val_ev
-- name    : Formalism.FourierDecayAlt.Q.QRR.val_ev
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:51:13.566133+00:00
-- url     : https://prove2.me/theorems/01207297-2461-402f-ab89-342bc005f322
-- title:
--   QRR: val ev
-- statement:
--   The QRR construction uses the val ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L208-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L208-L218

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

theorem Formalism.FourierDecayAlt.Q.QRR.val_ev (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) (j : Fin (mdim k r l.succ)) :
    ell k r z (Matrix.single (eI k r l) (posL k r l.succ j) 1) +
      star (ell k r z (dag k r (Matrix.single (eI k r l) (posL k r l.succ j) 1))) = xv k r z l.succ j := by sorry
