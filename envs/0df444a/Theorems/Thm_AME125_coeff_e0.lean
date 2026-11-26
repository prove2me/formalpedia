-- Prove2me | Theorems.Thm_AME125_coeff_e0
-- name    : AME125.coeff_e0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:14:37.543082+00:00
-- url     : https://prove2.me/theorems/ef8eaf4b-1038-53df-915b-ab0f387195b1
-- title:
--   AME125: coeff e0
-- statement:
--   No traced level is coupled to the difference `e0 - 0`.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Control.lean#L39-L58
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Control.lean#L39-L58

module
public import Definitions.Def_AME125_Certificate
public import Definitions.Def_AME125_Control
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.coeff_e0 :
    coeff (Nat.div_le_self 12 2) (controlU + controlUᵀ) (toZ e0 - toZ (0 : Config 6 5)) = 0 := by sorry
