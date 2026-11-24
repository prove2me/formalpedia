-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_update_add_single
-- name    : Formalism.IndefR.Tow.OrbStPf.update_add_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:22.727467+00:00
-- url     : https://prove2.me/theorems/408c5c20-4fcf-4157-9f44-6de2636b9a99
-- title:
--   Orb St Pf: update add single
-- statement:
--   The Orb St Pf construction uses the update add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L119-L122

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

theorem Formalism.IndefR.Tow.OrbStPf.update_add_single {i j : Fin N} (hij : i ≠ j) (r : Fin N → ℝ) (s t : ℝ) :
    Function.update (r + t • Pi.single i 1) j s = Function.update r j s + t • Pi.single i 1 := by sorry
