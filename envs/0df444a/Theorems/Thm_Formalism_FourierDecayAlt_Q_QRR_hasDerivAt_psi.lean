-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_hasDerivAt_psi
-- name    : Formalism.FourierDecayAlt.Q.QRR.hasDerivAt_psi
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:46:45.284869+00:00
-- url     : https://prove2.me/theorems/04d15c53-2a18-4599-beb2-68d0f3599752
-- title:
--   QRR: has Deriv At psi
-- statement:
--   The QRR construction uses the has Deriv At psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/PatEntryZero.lean#L305-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/PatEntryZero.lean#L305-L323

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

theorem Formalism.FourierDecayAlt.Q.QRR.hasDerivAt_psi (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (X : Mx k r) :
    HasDerivAt (fun t : ℝ => psi k r z cStd (NormedSpace.exp ((t : ℂ) • X)))
      (ell k r z X - star (ell k r z X)) 0 := by sorry
