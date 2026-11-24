-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_esI_zero
-- name    : Formalism.FourierDecayAlt.Q.QRR.esI_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:07:07.064691+00:00
-- url     : https://prove2.me/theorems/f03452ba-373b-4027-841f-a89f2f72ae58
-- title:
--   QRR: es I zero
-- statement:
--   The QRR construction uses the es I zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L193-L195

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

theorem Formalism.FourierDecayAlt.Q.QRR.esI_zero (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) : z (esI k r l) = 0 := by sorry
