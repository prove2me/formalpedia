-- Prove2me | Theorems.Thm_Erdos266_prod_lower
-- name    : Erdos266.prod_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:39:02.192724+00:00
-- url     : https://prove2.me/theorems/f8a3e9e1-6b96-55d5-a7a4-62276c91cbbd
-- title:
--   Erdos266: prod lower
-- statement:
--   Lower bound: with `B ≤ N/2`, every factor is at least `N/2`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/SlopeLemma.lean#L86-L94
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/SlopeLemma.lean#L86-L94

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_SlopeLemma
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.prod_lower {ι : Type*} {s : Finset ι} {c : ι → ℝ} {N B : ℝ}
    (hB : 0 ≤ B) (hB2 : B ≤ N / 2) (hc : ∀ j ∈ s, |c j| ≤ B) :
    (N / 2) ^ s.card ≤ ∏ j ∈ s, (N + c j) := by sorry
