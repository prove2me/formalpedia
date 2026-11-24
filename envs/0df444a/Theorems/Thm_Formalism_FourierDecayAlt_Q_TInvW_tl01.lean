-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tl01
-- name    : Formalism.FourierDecayAlt.Q.TInvW.tl01
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:34:03.740847+00:00
-- url     : https://prove2.me/theorems/b17e8d93-b470-452b-a449-3d7332dee57c
-- title:
--   TInv W: tl01
-- statement:
--   The TInv W construction uses the tl01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L372-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L372-L375

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

theorem Formalism.FourierDecayAlt.Q.TInvW.tl01 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 0 1 f =
      -(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i) f) := by sorry
