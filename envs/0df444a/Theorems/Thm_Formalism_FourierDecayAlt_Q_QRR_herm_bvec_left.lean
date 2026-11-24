-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_herm_bvec_left
-- name    : Formalism.FourierDecayAlt.Q.QRR.herm_bvec_left
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:46:17.137425+00:00
-- url     : https://prove2.me/theorems/e083526b-55e6-4e02-9909-a909bfbfd99e
-- title:
--   QRR: herm bvec left
-- statement:
--   The QRR construction uses the herm bvec left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L202-L206

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

theorem Formalism.FourierDecayAlt.Q.QRR.herm_bvec_left (x : Fin (2 * r + k + 1) → ℂ) (v : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec v) x = star (x (WeylGroupFacts.tau k r v)) * WeylGroupFacts.sgn k r v := by sorry
