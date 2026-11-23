-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_contDiff_pds
-- name    : Formalism.IndefR.Tow.OrbStPf.contDiff_pds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:59.067172+00:00
-- url     : https://prove2.me/theorems/55782bb1-d607-4b3d-9633-5436f1112b36
-- title:
--   Orb St Pf: cont Diff pds
-- statement:
--   The Orb St Pf construction uses the cont Diff pds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L25-L29

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

theorem Formalism.IndefR.Tow.OrbStPf.contDiff_pds (L : List (Fin N)) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (pds L f) := by sorry
