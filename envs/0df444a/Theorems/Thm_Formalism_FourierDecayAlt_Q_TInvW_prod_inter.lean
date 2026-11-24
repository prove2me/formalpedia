-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_prod_inter
-- name    : Formalism.FourierDecayAlt.Q.TInvW.prod_inter
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:52:57.115792+00:00
-- url     : https://prove2.me/theorems/afb78050-7272-4f3d-8138-7ea88438986a
-- title:
--   TInv W: prod inter
-- statement:
--   The TInv W construction uses the prod inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L64-L71

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

theorem Formalism.FourierDecayAlt.Q.TInvW.prod_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b)
    (l : List (ℂ × Fin n × Fin n)) :
    (l.map fun p => Tm E p.1 p.2.1 p.2.2).prod * R = R * (l.map fun p => Tm E' p.1 p.2.1 p.2.2).prod := by sorry
