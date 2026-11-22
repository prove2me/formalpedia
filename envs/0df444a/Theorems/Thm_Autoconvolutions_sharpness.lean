-- Prove2me | Theorems.Thm_Autoconvolutions_sharpness
-- name    : Autoconvolutions.sharpness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:06.5478+00:00
-- url     : https://prove2.me/theorems/6d82d52b-38d1-4801-8c67-7ef14bc6bddc
-- title:
--   Autoconvolutions: sharpness
-- statement:
--   Theorem 1 of Crmarić, Kovač and Rupčić. Section 2 chooses a rational
--   alphabet ratio close to one, then a truncation level, then the polynomial
--   exponent. Scaling the two alphabets preserves their selected ratio.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Solution.lean#L15-L62
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Solution.lean#L15-L62

module
public import Definitions.Def_Autoconvolutions_Main
public import Definitions.Def_Autoconvolutions_Solution
set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions
open Construction Filter Finset
open scoped Topology

theorem Autoconvolutions.sharpness (ε : ℝ) (hε : 0 < ε) :
    ∃ (d : ℕ) (p : Fin (d + 1) → ℝ),
      (∀ j, 0 ≤ p j) ∧ (∃ j, 0 < p j) ∧
      1 - ε < ratio (step d p) := by sorry
