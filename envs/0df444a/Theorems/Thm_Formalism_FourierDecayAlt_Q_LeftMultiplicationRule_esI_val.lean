-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_esI_val
-- name    : Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.esI_val
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:43:02.132959+00:00
-- url     : https://prove2.me/theorems/e42e2d92-61c0-474a-ad3b-0421bf505c3b
-- title:
--   Left Multiplication Rule: es I val
-- statement:
--   The Left Multiplication Rule construction uses the es I val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/MulApplyS.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/MulApplyS.lean#L22-L22

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.esI_val (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := by sorry
