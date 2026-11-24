-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_exp_hpart1_mem
-- name    : Formalism.FourierDecayAlt.Q.TInvW.exp_hpart1_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:34:34.180806+00:00
-- url     : https://prove2.me/theorems/cda5833e-d2fb-41d2-965a-bef712c4cb46
-- title:
--   TInv W: exp hpart1 mem
-- statement:
--   The TInv W construction uses the exp hpart1 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceCongruence.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceCongruence.lean#L168-L170

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

theorem Formalism.FourierDecayAlt.Q.TInvW.exp_hpart1_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := by sorry
