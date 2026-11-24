-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_contDiff_pd
-- name    : Formalism.IndefR.Tow.OrbStPf.contDiff_pd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:10.765199+00:00
-- url     : https://prove2.me/theorems/2279296b-2da2-4c55-aaa8-e5b7542cba1d
-- title:
--   Orb St Pf: cont Diff pd
-- statement:
--   The Orb St Pf construction uses the cont Diff pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L21-L23

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

theorem Formalism.IndefR.Tow.OrbStPf.contDiff_pd (i : Fin N) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (pd i f) := by sorry
