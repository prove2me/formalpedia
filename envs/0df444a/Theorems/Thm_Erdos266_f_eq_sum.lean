-- Prove2me | Theorems.Thm_Erdos266_f_eq_sum
-- name    : Erdos266.f_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:28.253254+00:00
-- url     : https://prove2.me/theorems/0df11e34-0ac0-41f4-8e7d-c5c0db260b15
-- title:
--   Erdos266: f eq sum
-- statement:
--   The partial-fraction identity away from the poles.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Defs.lean#L56-L105
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Defs.lean#L56-L105

module
public import Definitions.Def_Erdos266_Enumeration
public import Definitions.Def_Erdos266_Defs
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.f_eq_sum {i : ℕ} (hi : 1 ≤ i) {x : ℝ}
    (hx : ∀ j ∈ range i, x + (tSeq j : ℝ) ≠ 0) :
    f i x = ∑ j ∈ range i, (m i j : ℝ) * (x + (tSeq j : ℝ))⁻¹ := by sorry
