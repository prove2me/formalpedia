-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_single
-- name    : Formalism.FourierDecayAlt.Q.QRR.pat_single
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:07:39.313016+00:00
-- url     : https://prove2.me/theorems/13788d59-aadf-41a0-9a6d-7466dc190e80
-- title:
--   QRR: pat single
-- statement:
--   The QRR construction uses the pat single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L135-L144

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

theorem Formalism.FourierDecayAlt.Q.QRR.pat_single (l : Fin r) (a b : Fin (2 * r + k + 1)) (c : ℂ)
    (h : (a.val = l.val ∧ l.val < b.val ∧ b.val ≤ 2 * r + k - l.val) ∨
      (b.val = 2 * r + k - l.val ∧ l.val ≤ a.val ∧ a.val < 2 * r + k - l.val)) :
    Pat k r l (Matrix.single a b c) := by sorry
