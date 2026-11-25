-- Prove2me | Theorems.Thm_Erdos699_choose_dvd_gcd_mul
-- name    : Erdos699.choose_dvd_gcd_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:39.700444+00:00
-- url     : https://prove2.me/theorems/02ee8a78-03d5-45da-b8da-3798a4db67de
-- title:
--   Erdos699: choose dvd gcd mul
-- statement:
--   The identity `C(n, j) C(j, i) = C(n, i) C(n - i, j - i)` gives
--   `C(n, i) ∣ gcd(C(n, i), C(n, j)) · C(j, i)` (Erdős and Szekeres).
--
--   Source: https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L72-L77
-- source:
--   https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Erdos699/Basic.lean#L72-L77

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic
set_option autoImplicit false
@[expose] public section
public section
open Erdos699

theorem Erdos699.choose_dvd_gcd_mul {n i j : ℕ} (hij : i ≤ j) :
    n.choose i ∣ Nat.gcd (n.choose i) (n.choose j) * j.choose i := by sorry
