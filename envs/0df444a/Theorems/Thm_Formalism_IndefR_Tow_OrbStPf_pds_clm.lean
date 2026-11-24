-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_clm
-- name    : Formalism.IndefR.Tow.OrbStPf.pds_clm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:06.735764+00:00
-- url     : https://prove2.me/theorems/40992094-365c-4d90-a533-1f81a5acb054
-- title:
--   Orb St Pf: pds clm
-- statement:
--   The Orb St Pf construction uses the pds clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L81-L87

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

theorem Formalism.IndefR.Tow.OrbStPf.pds_clm (L : List (Fin N)) (A : H →L[ℝ] H) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pds L (fun p => A (f p)) = fun p => A (pds L f p) := by sorry
