-- Prove2me | Theorems.Thm_Erdos699_choose_mul_pow_le
-- name    : Erdos699.choose_mul_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:39.933331+00:00
-- url     : https://prove2.me/theorems/0f4ff546-1b9f-4e48-95ee-f1c7a6d4e8b0
-- title:
--   Erdos699: choose mul pow le
-- statement:
--   For `j ≤ n`: `C(j, i) · n^i ≤ C(n, i) · j^i`, i.e. `C(n, i) / C(j, i) ≥ (n / j)^i`.
--
--   Source: https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L63-L68
-- source:
--   https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L63-L68

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic
set_option autoImplicit false
@[expose] public section
public section
open Erdos699

theorem Erdos699.choose_mul_pow_le {i j n : ℕ} (hjn : j ≤ n) :
    j.choose i * n ^ i ≤ n.choose i * j ^ i := by sorry
