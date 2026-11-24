-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_update
-- name    : Formalism.IndefR.Tow.OrbStPf.pd_update
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:13.863775+00:00
-- url     : https://prove2.me/theorems/a3fe9958-65ce-4e57-8cba-bd3776e746af
-- title:
--   Orb St Pf: pd update
-- statement:
--   The Orb St Pf construction uses the pd update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L133-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L133-L141

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

theorem Formalism.IndefR.Tow.OrbStPf.pd_update (i j : Fin N) (hij : i ≠ j) (s : ℝ) {g : (Fin N → ℝ) → H} (hg : Differentiable ℝ g) :
    pd i (fun r => g (Function.update r j s)) = fun r => pd i g (Function.update r j s) := by sorry
