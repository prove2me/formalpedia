-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_rdV_right
-- name    : Formalism.FourierDecayAlt.Q.TInvW.rdV_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:54:01.229024+00:00
-- url     : https://prove2.me/theorems/fea468a4-7e6a-47d3-81e6-247f0a3c6a77
-- title:
--   TInv W: rd V right
-- statement:
--   The TInv W construction uses the rd V right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceCongruence.lean#L214-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceCongruence.lean#L214-L225

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.TInvW.rdV_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X s' g : Mx k r) (f : Mx k r → E)
    (hu1 : s' * s'⁻¹ = 1) (hu2 : s'⁻¹ * s' = 1) :
    RdV X (fun x => f (x * s')) g = RdV (s'⁻¹ * X * s') f (g * s') := by sorry
