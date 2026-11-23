-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_eq_deriv
-- name    : Formalism.IndefR.Tow.OrbStPf.pd_eq_deriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:42:43.315023+00:00
-- url     : https://prove2.me/theorems/486347fb-7525-4fee-9119-0ff0e49f828f
-- title:
--   Orb St Pf: pd eq deriv
-- statement:
--   The Orb St Pf construction uses the pd eq deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L44-L46

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Formalism Formalism.IndefR Formalism.IndefR.Tow Formalism.IndefR.Tow.OrbStPf
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem Formalism.IndefR.Tow.OrbStPf.pd_eq_deriv (i : Fin N) {f : (Fin N → ℝ) → H} (p : Fin N → ℝ) (hf : DifferentiableAt ℝ f p) :
    pd i f p = deriv (fun t : ℝ => f (p + t • Pi.single i 1)) 0 := by sorry
