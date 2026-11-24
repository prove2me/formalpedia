-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_val_ve
-- name    : Formalism.FourierDecayAlt.Q.QRR.val_ve
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:19.610576+00:00
-- url     : https://prove2.me/theorems/60c749ed-5bc0-4889-a71d-425422ecb358
-- title:
--   QRR: val ve
-- statement:
--   The QRR construction uses the val ve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L220-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L220-L240

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

theorem Formalism.FourierDecayAlt.Q.QRR.val_ve (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) (j : Fin (mdim k r l.succ)) :
    ell k r z (Matrix.single (posL k r l.succ j) (esI k r l) 1) +
      star (ell k r z (dag k r (Matrix.single (posL k r l.succ j) (esI k r l) 1))) = xbv k r z l.succ j := by sorry
