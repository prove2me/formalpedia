-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresLie_posL_ne
-- name    : Formalism.FourierDecayAlt.Q.TPresLie.posL_ne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:54:02.922568+00:00
-- url     : https://prove2.me/theorems/30b5c385-b1c0-4d2c-9f10-67197ec18ee6
-- title:
--   TPres Lie: pos L ne
-- statement:
--   The TPres Lie construction uses the pos L ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/HasDerivAtExt.lean#L142-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/HasDerivAtExt.lean#L142-L150

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

theorem Formalism.FourierDecayAlt.Q.TPresLie.posL_ne (i : Fin (r + 1)) (q : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    eI k r a ≠ posL k r i q ∧ esI k r a ≠ posL k r i q := by sorry
