-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_coord
-- name    : Formalism.FourierDecayAlt.Q.TInvW.coord
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:50:55.81638+00:00
-- url     : https://prove2.me/theorems/26d7639b-973b-4d89-b754-9592271ab2a2
-- title:
--   TInv W: coord
-- statement:
--   The TInv W construction uses the coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L86-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L86-L110

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

theorem Formalism.FourierDecayAlt.Q.TInvW.coord {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (c d : Fin (2 * r + k + 1))
    (hcd : ∀ w, (Hpk k r *ᵥ w) c = w d) (hfix : g *ᵥ bvec c = bvec c) (v : Fin (2 * r + k + 1) → ℂ) :
    (g *ᵥ v) d = v d := by sorry
