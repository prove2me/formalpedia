-- Prove2me | Theorems.Thm_AME125_quad_add
-- name    : AME125.quad_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:04.269668+00:00
-- url     : https://prove2.me/theorems/857efcc7-ecc0-5adf-a98b-b02e636578b4
-- title:
--   AME125: quad add
-- statement:
--   `xᵀ U x` at `y + w`, expanded: the cross terms are `∑ j, (∑ i, w i · S i j) · y j` with
--   `S = U + Uᵀ`.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L86-L98
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L86-L98

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.quad_add {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 5)) (y w : Fin n → ZMod 5) :
    quad U (y + w) = quad U y + quad U w + ∑ j, (∑ i, w i * (U + Uᵀ) i j) * y j := by sorry
