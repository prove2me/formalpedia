-- Prove2me | Theorems.Thm_AME125_sum_range_twelve
-- name    : AME125.sum_range_twelve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:13:15.327836+00:00
-- url     : https://prove2.me/theorems/664e3f44-aaff-55e5-9d19-66437598b6fe
-- title:
--   AME125: sum range twelve
-- statement:
--   A sum over `List.range 12` is a sum over `Fin 12`.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L117-L119
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L117-L119

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix

theorem AME125.sum_range_twelve {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ((List.range 12).map f).sum = ∑ j : Fin 12, f j := by sorry
