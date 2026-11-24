-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_ell_single_row
-- name    : Formalism.FourierDecayAlt.Q.QRR.ell_single_row
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:39:02.239269+00:00
-- url     : https://prove2.me/theorems/0fb4cda5-5e8c-4818-9ee6-752f7345475f
-- title:
--   QRR: ell single row
-- statement:
--   The QRR construction uses the ell single row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L34-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L34-L55

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

theorem Formalism.FourierDecayAlt.Q.QRR.ell_single_row (z : Fin (2 * r + k + 1) → ℂ) (l : Fin r) (b : Fin (2 * r + k + 1)) (c : ℂ) :
    ell k r z (Matrix.single (eI k r l) b c) =
      if h : l.val + 1 < r then (if b = eI k r ⟨l.val + 1, h⟩ then c else 0) else c * z b := by sorry
