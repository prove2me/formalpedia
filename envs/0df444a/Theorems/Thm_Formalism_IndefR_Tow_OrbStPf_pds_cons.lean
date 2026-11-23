-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_cons
-- name    : Formalism.IndefR.Tow.OrbStPf.pds_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:36.206912+00:00
-- url     : https://prove2.me/theorems/faf96250-7c1e-47f6-8d6e-57d0b901ce11
-- title:
--   Orb St Pf: pds cons
-- statement:
--   The Orb St Pf construction uses the pds cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean#L18-L19

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

theorem Formalism.IndefR.Tow.OrbStPf.pds_cons (i : Fin N) (L : List (Fin N)) (f : (Fin N → ℝ) → H) :
    pds (i :: L) f = pd i (pds L f) := by sorry

attribute [defeq] Formalism.IndefR.Tow.OrbStPf.pds_cons
