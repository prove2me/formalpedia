-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_entry_zero
-- name    : Formalism.FourierDecayAlt.Q.QRR.pat_entry_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:47:25.114736+00:00
-- url     : https://prove2.me/theorems/e65ee8da-cf5c-400c-a0a1-e8430c4d8c1c
-- title:
--   QRR: pat entry zero
-- statement:
--   The QRR construction uses the pat entry zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/PatEntryZero.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/PatEntryZero.lean#L117-L121

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.QRR.pat_entry_zero {l : Fin r} {Y : Mx k r} (hY : Pat k r l Y) (i j : Fin (2 * r + k + 1))
    (h : ¬ ((i.val = l.val ∧ l.val < j.val ∧ j.val ≤ 2 * r + k - l.val) ∨
      (j.val = 2 * r + k - l.val ∧ l.val ≤ i.val ∧ i.val < 2 * r + k - l.val))) : Y i j = 0 := by sorry
