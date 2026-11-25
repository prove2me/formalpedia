-- Prove2me | Theorems.Thm_Erdos1063_dvd_W
-- name    : Erdos1063.dvd_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:35:24.168868+00:00
-- url     : https://prove2.me/theorems/46e7d71e-a1ae-48b2-8325-fe88b05983e8
-- title:
--   Erdos1063: dvd W
-- statement:
--   `k ∣ W'_k`, since `p ^ v_p(k) ∣ p ^ (v_p(k) + ⌊log_p (k-1)⌋)` for every `p ∣ k`.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L244-L250
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L244-L250

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.dvd_W {k : ℕ} (hk : k ≠ 0) : k ∣ W k := by sorry
