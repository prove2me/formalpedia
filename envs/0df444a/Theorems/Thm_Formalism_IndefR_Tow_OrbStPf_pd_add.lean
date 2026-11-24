-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_add
-- name    : Formalism.IndefR.Tow.OrbStPf.pd_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:13.009176+00:00
-- url     : https://prove2.me/theorems/92b86b45-eec8-4659-b44b-a0c32246a184
-- title:
--   Orb St Pf: pd add
-- statement:
--   The Orb St Pf construction uses the pd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L89-L94

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

theorem Formalism.IndefR.Tow.OrbStPf.pd_add (i : Fin N) {f g : (Fin N → ℝ) → H} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    pd i (fun p => f p + g p) = fun p => pd i f p + pd i g p := by sorry
