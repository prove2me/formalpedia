-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_unit
-- name    : Formalism.FourierDecayAlt.Q.TInvW.glev_unit
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:14:33.616304+00:00
-- url     : https://prove2.me/theorems/e2d5ea64-866e-4639-92b8-3868fdabe277
-- title:
--   TInv W: glev unit
-- statement:
--   The TInv W construction uses the glev unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L29-L36

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

theorem Formalism.FourierDecayAlt.Q.TInvW.glev_unit {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by sorry
