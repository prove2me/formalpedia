-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_sum_posL
-- name    : Formalism.FourierDecayAlt.Q.TInvW.sum_posL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:53.923138+00:00
-- url     : https://prove2.me/theorems/9d731b50-39b2-4c98-8db0-53d14ce578be
-- title:
--   TInv W: sum pos L
-- statement:
--   The TInv W construction uses the sum pos L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L151-L154

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.TInvW.sum_posL {M : Type*} [AddCommMonoid M] {i : Fin (r + 1)} (F : Fin (2 * r + k + 1) → M)
    (hF : ∀ q, (∀ c, q ≠ posL k r i c) → F q = 0) :
    ∑ q, F q = ∑ c : Fin (mdim k r i), F (posL k r i c) := by sorry
