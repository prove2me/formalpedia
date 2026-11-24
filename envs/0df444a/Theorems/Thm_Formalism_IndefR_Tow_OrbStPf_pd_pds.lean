-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_pds
-- name    : Formalism.IndefR.Tow.OrbStPf.pd_pds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:11.552818+00:00
-- url     : https://prove2.me/theorems/f5f35b7b-7b97-4602-951e-1625b5cf55ef
-- title:
--   Orb St Pf: pd pds
-- statement:
--   The Orb St Pf construction uses the pd pds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L65-L71

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

theorem Formalism.IndefR.Tow.OrbStPf.pd_pds (k : Fin N) (L : List (Fin N)) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pd k (pds L f) = pds L (pd k f) := by sorry
