-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_single
-- name    : Formalism.FourierDecayAlt.Q.QRR.dag_single
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:07:09.135961+00:00
-- url     : https://prove2.me/theorems/783c06fb-f093-42fd-9ba6-15e0345e0ecb
-- title:
--   QRR: dag single
-- statement:
--   The QRR construction uses the dag single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L119-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L119-L133

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

theorem Formalism.FourierDecayAlt.Q.QRR.dag_single (a b : Fin (2 * r + k + 1)) (c : ℂ) :
    dag k r (Matrix.single a b c) = Matrix.single (WeylGroupFacts.tau k r b) (WeylGroupFacts.tau k r a)
      (WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r b) * star c * WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r a)) := by sorry
