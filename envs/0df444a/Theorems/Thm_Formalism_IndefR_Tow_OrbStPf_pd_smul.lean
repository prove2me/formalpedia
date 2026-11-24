-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_smul
-- name    : Formalism.IndefR.Tow.OrbStPf.pd_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:07.970547+00:00
-- url     : https://prove2.me/theorems/607d6f49-220b-4738-9988-bde8e285cff8
-- title:
--   Orb St Pf: pd smul
-- statement:
--   The Orb St Pf construction uses the pd smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L96-L101

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

theorem Formalism.IndefR.Tow.OrbStPf.pd_smul (i : Fin N) (c : ℝ) {f : (Fin N → ℝ) → H} (hf : Differentiable ℝ f) :
    pd i (fun p => c • f p) = fun p => c • pd i f p := by sorry
