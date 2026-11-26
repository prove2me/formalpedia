-- Prove2me | Theorems.Thm_AME125_ame125State_isAME
-- name    : AME125.ame125State_isAME
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:14:47.431302+00:00
-- url     : https://prove2.me/theorems/acc836db-cb5b-5c0d-940a-7a6bc4caac52
-- title:
--   AME125: ame125 State is AME
-- statement:
--   The witness is absolutely maximally entangled.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/FormalTarget.lean#L30-L31
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/FormalTarget.lean#L30-L31

module
public import Definitions.Def_AME125_Certificate
public import Definitions.Def_AME125_FormalTarget
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35

theorem AME125.ame125State_isAME : IsAME ame125State := by sorry
