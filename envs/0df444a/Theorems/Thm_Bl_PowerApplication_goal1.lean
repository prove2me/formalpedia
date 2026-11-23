-- Prove2me | Theorems.Thm_Bl_PowerApplication_goal1
-- name    : Bl.PowerApplication.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:53.00641+00:00
-- url     : https://prove2.me/theorems/92a12133-0968-4100-8aaa-946328774600
-- title:
--   Power Application: goal1
-- statement:
--   The Power Application construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PowerApplication/PowApp.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PowerApplication/PowApp.lean#L15-L21

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
open Bl Bl.PowerApplication
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

theorem Bl.PowerApplication.goal1 {T : Module.End ℂ Y} {z : ℂ} {f : Y} (hf : T f = z • f) (p : ℂ[X]) :
    aeval T p f = p.eval z • f := by sorry
