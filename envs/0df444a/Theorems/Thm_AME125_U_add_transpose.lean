-- Prove2me | Theorems.Thm_AME125_U_add_transpose
-- name    : AME125.U_add_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:13:11.7523+00:00
-- url     : https://prove2.me/theorems/997cfd18-79d8-4fdd-91a6-8a0e11217716
-- title:
--   AME125: U add transpose
-- statement:
--   `theta` is symmetric, so `U + Uᵀ` agrees with it off the diagonal.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L45-L49
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L45-L49

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix

theorem AME125.U_add_transpose (i j : Fin 12) (h : i ≠ j) : (U + Uᵀ) i j = theta i j := by sorry
