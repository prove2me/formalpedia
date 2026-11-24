-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_tau_eI
-- name    : Formalism.FourierDecayAlt.Q.QRR.tau_eI
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:37.435915+00:00
-- url     : https://prove2.me/theorems/537e0286-f8ac-47cc-82e4-1f42055234f8
-- title:
--   QRR: tau e I
-- statement:
--   The QRR construction uses the tau e I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L154-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L154-L160

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

theorem Formalism.FourierDecayAlt.Q.QRR.tau_eI (l : Fin r) : WeylGroupFacts.tau k r (eI k r l) = esI k r l := by sorry
