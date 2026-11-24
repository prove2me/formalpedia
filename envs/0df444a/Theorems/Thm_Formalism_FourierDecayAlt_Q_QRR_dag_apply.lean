-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_apply
-- name    : Formalism.FourierDecayAlt.Q.QRR.dag_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:46:31.001171+00:00
-- url     : https://prove2.me/theorems/46d298ed-645c-42c2-8ff2-ff4c2fc96673
-- title:
--   QRR: dag apply
-- statement:
--   The QRR construction uses the dag apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/PatEntryZero.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/PatEntryZero.lean#L63-L66

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

theorem Formalism.FourierDecayAlt.Q.QRR.dag_apply (Z : Mx k r) (i j : Fin (2 * r + k + 1)) :
    dag k r Z i j = WeylGroupFacts.sgn k r i * star (Z (WeylGroupFacts.tau k r j) (WeylGroupFacts.tau k r i)) * WeylGroupFacts.sgn k r j := by sorry
