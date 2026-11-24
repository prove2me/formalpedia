-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_inv_fix
-- name    : Formalism.FourierDecayAlt.Q.TInvW.inv_fix
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:14:42.852132+00:00
-- url     : https://prove2.me/theorems/5a718409-dd3e-480f-8858-ca2614788abd
-- title:
--   TInv W: inv fix
-- statement:
--   The TInv W construction uses the inv fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L38-L41

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

theorem Formalism.FourierDecayAlt.Q.TInvW.inv_fix {g : Mx k r} (hu : g⁻¹ * g = 1) {v : Fin (2 * r + k + 1) → ℂ} (h : g *ᵥ v = v) :
    g⁻¹ *ᵥ v = v := by sorry
