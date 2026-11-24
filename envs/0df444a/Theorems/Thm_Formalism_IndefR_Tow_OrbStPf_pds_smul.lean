-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_smul
-- name    : Formalism.IndefR.Tow.OrbStPf.pds_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:14.394795+00:00
-- url     : https://prove2.me/theorems/bd83bfc2-26c4-431f-9941-be923ac5b51e
-- title:
--   Orb St Pf: pds smul
-- statement:
--   The Orb St Pf construction uses the pds smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L111-L117

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

theorem Formalism.IndefR.Tow.OrbStPf.pds_smul (L : List (Fin N)) (c : ℝ) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pds L (fun p => c • f p) = fun p => c • pds L f p := by sorry
