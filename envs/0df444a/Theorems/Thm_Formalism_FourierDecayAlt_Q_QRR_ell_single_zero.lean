-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_ell_single_zero
-- name    : Formalism.FourierDecayAlt.Q.QRR.ell_single_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:06:43.277662+00:00
-- url     : https://prove2.me/theorems/5e7d5400-3593-42e1-a678-e18335b10b12
-- title:
--   QRR: ell single zero
-- statement:
--   The QRR construction uses the ell single zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L20-L32

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

theorem Formalism.FourierDecayAlt.Q.QRR.ell_single_zero (z : Fin (2 * r + k + 1) → ℂ) (a b : Fin (2 * r + k + 1)) (c : ℂ)
    (hb : r ≤ b.val) (hzb : z b = 0) : ell k r z (Matrix.single a b c) = 0 := by sorry
