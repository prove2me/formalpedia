-- Prove2me | Theorems.Thm_AaronsonAmbainis_Pack_scaled_bound
-- name    : AaronsonAmbainis.Pack.scaled_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:12.370746+00:00
-- url     : https://prove2.me/theorems/33d989ee-1cb9-4ce4-bf28-3d8ee1b96e9c
-- title:
--   Pack: scaled bound
-- statement:
--   The packing bound before the limit, from the block inequality with `N = M ^ 2` and
--   `m = ⌈π M / 2⌉₊`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Scaled.lean#L42-L85
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Scaled.lean#L42-L85

import Definitions.Def_AaronsonAmbainis_Pack_Gate
import Definitions.Def_AaronsonAmbainis_Pack_Blocks
import Definitions.Def_AaronsonAmbainis_Pack_Scaled
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
open Finset

theorem AaronsonAmbainis.Pack.scaled_bound (hB : BlockInequality) (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hd : HasDegreeLE f d) (x : Cube ι)
    (κ : Finset ι → ℝ) (hκ : ∀ S, 0 ≤ κ S)
    (hpack : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1)
    (M : ℕ) (hM : 0 < M) :
    (M : ℝ) ^ 2 * ∑ S, κ S * |f x - f (flipSet x S)|
      ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + ∑ S, |f x - f (flipSet x S)| := by sorry
