-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_second_capelli_minor_intertwines
-- name    : Formalism.FourierDecayAlt.Q.TInvW.second_capelli_minor_intertwines
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:22.019977+00:00
-- url     : https://prove2.me/theorems/758a3bb2-560c-4018-8cd0-75a5202b2b1f
-- title:
--   TInv W: second capelli minor intertwines
-- statement:
--   The TInv W construction uses the second capelli minor intertwines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L91-L95

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem Formalism.FourierDecayAlt.Q.TInvW.second_capelli_minor_intertwines (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a a' β β' : Fin n → ℂ) : chat2A E u a a' β β' * R = R * chat2A E' u a a' β β' := by sorry
