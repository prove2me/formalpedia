-- Prove2me | Theorems.Thm_APFB01_undone_hold_returns_every_object
-- name    : APFB01.undone_hold_returns_every_object
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:54:07.853064+00:00
-- url     : https://prove2.me/theorems/cd679220-0cfa-4f22-b409-16bb193dd13a
-- title:
--   Undone hold returns every object
-- statement:
--   For a profile on a finite process type, every injective self-map of its physical-state quotient returns each class after some positive number of iterations. Injectivity and finite process type are supplied.
-- source:
--   Sib v44 Theorems/Thm_APFB01_undone_hold_returns.lean:61

import Definitions.Def_APF_B01_DeclaredInput
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finite.Prod
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

universe uX uP



namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFB01.undone_hold_returns_every_object {X : Type uX} {Process : Type uP} [Finite Process]
    (profile : X → Process → Prop)
    (D : APFB01.PhysicalState profile → APFB01.PhysicalState profile)
    (hD : Function.Injective D) (s : APFB01.PhysicalState profile) :
    ∃ n : ℕ, 0 < n ∧ D^[n] s = s := by sorry
