-- Prove2me | Theorems.Thm_Erdos266_abs_prod_sub_pow_le
-- name    : Erdos266.abs_prod_sub_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:38:39.506992+00:00
-- url     : https://prove2.me/theorems/7f09c9e4-e1e0-5e5c-972e-c9bfd8c73757
-- title:
--   Erdos266: abs prod sub pow le
-- statement:
--   A product of `card s` factors `N + cⱼ` with `|cⱼ| ≤ B ≤ N` differs from
--   `N ^ card s` by at most `(2 ^ card s - 1) · B · N ^ card s / N`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/SlopeLemma.lean#L46-L72
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/SlopeLemma.lean#L46-L72

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_SlopeLemma
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.abs_prod_sub_pow_le {ι : Type*} {s : Finset ι} {c : ι → ℝ} {N B : ℝ}
    (_hB : 0 ≤ B) (hBN : B ≤ N) (hN : 0 < N) (hc : ∀ j ∈ s, |c j| ≤ B) :
    |(∏ j ∈ s, (N + c j)) - N ^ s.card|
      ≤ (2 ^ s.card - 1) * B * N ^ s.card / N := by sorry
