-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_left_step
-- name    : Formalism.FourierDecayAlt.Q.TInvW.left_step
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:52:08.964052+00:00
-- url     : https://prove2.me/theorems/77a52bce-ca81-4e0a-bc05-e6acd36cb7fe
-- title:
--   TInv W: left step
-- statement:
--   The TInv W construction uses the left step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L388-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L388-L408

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

theorem Formalism.FourierDecayAlt.Q.TInvW.left_step (hL : QMinorLeftH) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Y : ℂ) (p q : Fin 2) (F : Mx k r → E) (s g : Mx k r)
    (hy : yv k r z i (s * g) = yv k r z i g) (hyb : ybv k r z i (s * g) = ybv k r z i g) :
    tL k r z z' i Y p q (fun x => F (s * x)) g = tL k r z z' i Y p q F (s * g) := by sorry
