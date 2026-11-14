-- Prove2me | Theorems.Thm_APFB01_physicalState_finite
-- name    : APFB01.physicalState_finite
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:53:09.867642+00:00
-- url     : https://prove2.me/theorems/6606bbf3-00d8-45cd-9936-c5d052fd3231
-- title:
--   Physicalstate finite
-- statement:
--   For any profile on a finite process type, the quotient identifying raw states with equal profiles is finite. Finiteness of the whole process type is an explicit hypothesis, not a consequence of finite capacity.
-- source:
--   Sib v44 Theorems/Thm_APFB01_undone_hold_returns.lean:31

import Definitions.Def_APF_B01_DeclaredInput
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finite.Prod
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

universe uX uP

theorem APFB01.physicalState_finite {X : Type uX} {Process : Type uP} [Finite Process]
    (profile : X → Process → Prop) : Finite (APFB01.PhysicalState profile) := by sorry
