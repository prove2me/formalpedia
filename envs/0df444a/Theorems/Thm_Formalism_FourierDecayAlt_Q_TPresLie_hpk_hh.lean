-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresLie_hpk_hh
-- name    : Formalism.FourierDecayAlt.Q.TPresLie.hpk_hh
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:58:41.56881+00:00
-- url     : https://prove2.me/theorems/dbebb849-4242-4c83-b24b-728667e87465
-- title:
--   TPres Lie: hpk hh
-- statement:
--   The TPres Lie construction uses the hpk hh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/HasDerivAtExt.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/HasDerivAtExt.lean#L23-L23

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.TPresLie.hpk_hh (A : Mx k r) : Hpk k r * (Hpk k r * A) = A := by sorry
