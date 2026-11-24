-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpart_cols
-- name    : Formalism.FourierDecayAlt.Q.TInvW.hpart_cols
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:33:48.166711+00:00
-- url     : https://prove2.me/theorems/4178b2e2-b300-4a36-882f-82706dd0d7ad
-- title:
--   TInv W: hpart cols
-- statement:
--   The TInv W construction uses the hpart cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceCongruence.lean#L141-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceCongruence.lean#L141-L166

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

theorem Formalism.FourierDecayAlt.Q.TInvW.hpart_cols (i : Fin (r + 1)) (p q : Fin (mdim k r i)) :
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) ∧
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) := by sorry
