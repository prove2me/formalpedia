-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresLie_unit_col
-- name    : Formalism.FourierDecayAlt.Q.TPresLie.unit_col
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:53:46.14904+00:00
-- url     : https://prove2.me/theorems/5a1bd4ae-9674-419c-9934-66411190fd6b
-- title:
--   TPres Lie: unit col
-- statement:
--   The TPres Lie construction uses the unit col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/HasDerivAtExt.lean#L126-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/HasDerivAtExt.lean#L126-L140

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

theorem Formalism.FourierDecayAlt.Q.TPresLie.unit_col (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcq : c ≠ posL k r i q) (hHc : Hpk k r (posL k r i p) c = 0) (x : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
    (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by sorry
