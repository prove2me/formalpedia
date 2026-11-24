-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresLie_skew_real
-- name    : Formalism.FourierDecayAlt.Q.TPresLie.skew_real
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:54:25.786303+00:00
-- url     : https://prove2.me/theorems/04b6b8c9-151c-4546-9dde-632179cf1aba
-- title:
--   TPres Lie: skew real
-- statement:
--   The TPres Lie construction uses the skew real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/HasDerivAtExt.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/HasDerivAtExt.lean#L43-L46

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

theorem Formalism.FourierDecayAlt.Q.TPresLie.skew_real (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r)) (t : ℝ) :
    ((t : ℂ) • X)ᴴ = -(Hpk k r * ((t : ℂ) • X) * Hpk k r) := by sorry
