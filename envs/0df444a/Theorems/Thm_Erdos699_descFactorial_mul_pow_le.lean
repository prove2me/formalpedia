-- Prove2me | Theorems.Thm_Erdos699_descFactorial_mul_pow_le
-- name    : Erdos699.descFactorial_mul_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:14.695718+00:00
-- url     : https://prove2.me/theorems/db7e24a2-7e9b-5aef-938c-344d3c990530
-- title:
--   Erdos699: desc Factorial mul pow le
-- statement:
--   For `j ≤ n`: `j(j-1)⋯(j-i+1) · n^i ≤ n(n-1)⋯(n-i+1) · j^i`.
--
--   Source: https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L48-L60
-- source:
--   https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L48-L60

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic
set_option autoImplicit false
@[expose] public section
public section
open Erdos699

theorem Erdos699.descFactorial_mul_pow_le {j n : ℕ} (hjn : j ≤ n) :
    ∀ i : ℕ, j.descFactorial i * n ^ i ≤ n.descFactorial i * j ^ i
  := by sorry
