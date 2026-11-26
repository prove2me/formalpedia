-- Prove2me | Theorems.Thm_Erdos266_exists_growth_enumeration
-- name    : Erdos266.exists_growth_enumeration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:12.248269+00:00
-- url     : https://prove2.me/theorems/69c547bc-9d9a-432e-9c37-b0378da87ee2
-- title:
--   Erdos266: exists growth enumeration
-- statement:
--   There is an enumeration of `ℚ` with linear growth: condition (7.1) of
--   [KoTa24], 0-indexed.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L136-L138
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L136-L138

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
set_option autoImplicit false
@[expose] public section
public section
open Erdos266

theorem Erdos266.exists_growth_enumeration :
    ∃ t : ℕ → ℚ, Function.Bijective t ∧ ∀ j : ℕ, |t j| ≤ (j : ℚ) + 1 := by sorry
