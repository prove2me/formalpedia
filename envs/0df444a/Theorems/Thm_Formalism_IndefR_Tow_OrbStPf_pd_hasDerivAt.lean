-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_hasDerivAt
-- name    : Formalism.IndefR.Tow.OrbStPf.pd_hasDerivAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:03.119079+00:00
-- url     : https://prove2.me/theorems/c7056691-251f-4698-8fed-f2841f31e103
-- title:
--   Orb St Pf: pd has Deriv At
-- statement:
--   The Orb St Pf construction uses the pd has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L35-L42

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

theorem Formalism.IndefR.Tow.OrbStPf.pd_hasDerivAt (i : Fin N) {f : (Fin N → ℝ) → H} (p : Fin N → ℝ) (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun t : ℝ => f (p + t • Pi.single i 1)) (pd i f p) 0 := by sorry
