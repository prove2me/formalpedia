-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_tau_esI
-- name    : Formalism.FourierDecayAlt.Q.QRR.tau_esI
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:07:11.572965+00:00
-- url     : https://prove2.me/theorems/ad8b2f5f-3841-4174-b92f-c851f3bf106d
-- title:
--   QRR: tau es I
-- statement:
--   The QRR construction uses the tau es I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L162-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L162-L173

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

theorem Formalism.FourierDecayAlt.Q.QRR.tau_esI (l : Fin r) : WeylGroupFacts.tau k r (esI k r l) = eI k r l := by sorry
