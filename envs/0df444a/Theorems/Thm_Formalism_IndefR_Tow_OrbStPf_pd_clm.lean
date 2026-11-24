-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_clm
-- name    : Formalism.IndefR.Tow.OrbStPf.pd_clm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:04.74984+00:00
-- url     : https://prove2.me/theorems/69d70e3c-df07-4d2c-b524-b9b23ca2c9f7
-- title:
--   Orb St Pf: pd clm
-- statement:
--   The Orb St Pf construction uses the pd clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L73-L79

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

theorem Formalism.IndefR.Tow.OrbStPf.pd_clm (i : Fin N) (A : H →L[ℝ] H) {f : (Fin N → ℝ) → H} (hf : Differentiable ℝ f) :
    pd i (fun p => A (f p)) = fun p => A (pd i f p) := by sorry
