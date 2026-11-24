-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_val_ees
-- name    : Formalism.FourierDecayAlt.Q.QRR.val_ees
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:12.163875+00:00
-- url     : https://prove2.me/theorems/5665bb90-2938-4c00-a921-002dce6a10e7
-- title:
--   QRR: val ees
-- statement:
--   The QRR construction uses the val ees property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L242-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L242-L246

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

theorem Formalism.FourierDecayAlt.Q.QRR.val_ees (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) :
    ell k r z (Matrix.single (eI k r l) (esI k r l) 1) +
      star (ell k r z (dag k r (Matrix.single (eI k r l) (esI k r l) 1))) = 0 := by sorry
