-- Prove2me | Theorems.Thm_Erdos266_abs_prod_le
-- name    : Erdos266.abs_prod_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:38:31.802026+00:00
-- url     : https://prove2.me/theorems/4831cb18-74c4-56c1-9308-5a565bdf24c9
-- title:
--   Erdos266: abs prod le
-- statement:
--   Upper bound: every factor is at most `2N`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/SlopeLemma.lean#L75-L83
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/SlopeLemma.lean#L75-L83

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_SlopeLemma
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.abs_prod_le {ι : Type*} {s : Finset ι} {c : ι → ℝ} {N B : ℝ}
    (hB : 0 ≤ B) (hBN : B ≤ N) (hc : ∀ j ∈ s, |c j| ≤ B) :
    |∏ j ∈ s, (N + c j)| ≤ (2 * N) ^ s.card := by sorry
