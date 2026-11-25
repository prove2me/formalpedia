-- Prove2me | Theorems.Thm_Erdos919_continuum_eq_aleph1_zero
-- name    : Erdos919.continuum_eq_aleph1_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:33:26.780576+00:00
-- url     : https://prove2.me/theorems/1ef2d02e-9c37-5f2e-8158-e5d4b31f3608
-- title:
--   Erdos919: continuum eq aleph1 zero
-- statement:
--   CH does not depend on the universe.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L844-L848
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L844-L848

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
universe v

theorem Erdos919.continuum_eq_aleph1_zero (h : (𝔠 : Cardinal.{v}) = ℵ₁) :
    (𝔠 : Cardinal.{0}) = ℵ₁ := by sorry
