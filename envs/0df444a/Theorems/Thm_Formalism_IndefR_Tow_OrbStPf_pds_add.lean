-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_add
-- name    : Formalism.IndefR.Tow.OrbStPf.pds_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:16.270452+00:00
-- url     : https://prove2.me/theorems/8a8c1e97-93da-4ab3-aadc-3609c0fb3cb0
-- title:
--   Orb St Pf: pds add
-- statement:
--   The Orb St Pf construction uses the pds add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L103-L109

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

theorem Formalism.IndefR.Tow.OrbStPf.pds_add (L : List (Fin N)) {f g : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    pds L (fun p => f p + g p) = fun p => pds L f p + pds L g p := by sorry
