-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_comm
-- name    : Formalism.IndefR.Tow.OrbStPf.pd_comm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:11.203635+00:00
-- url     : https://prove2.me/theorems/6f8d74ac-3f8c-4e1c-b245-064fe2a7a408
-- title:
--   Orb St Pf: pd comm
-- statement:
--   The Orb St Pf construction uses the pd comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L53-L63

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

theorem Formalism.IndefR.Tow.OrbStPf.pd_comm (i j : Fin N) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pd i (pd j f) = pd j (pd i f) := by sorry
