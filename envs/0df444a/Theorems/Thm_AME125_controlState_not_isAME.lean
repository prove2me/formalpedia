-- Prove2me | Theorems.Thm_AME125_controlState_not_isAME
-- name    : AME125.controlState_not_isAME
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:20:37.10823+00:00
-- url     : https://prove2.me/theorems/564e9647-7192-4dad-9040-ceb73e339baf
-- title:
--   AME125: control State not is AME
-- statement:
--   **The control state is not AME.**
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Control.lean#L61-L71
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Control.lean#L61-L71

module
public import Definitions.Def_AME125_Certificate
public import Definitions.Def_AME125_Control
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.controlState_not_isAME : ¬ IsAME controlState := by sorry
