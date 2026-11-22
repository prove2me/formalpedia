-- Prove2me | Theorems.Thm_AbstractLaminar_seam_of_adjacent
-- name    : AbstractLaminar.seam_of_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:01.632478+00:00
-- url     : https://prove2.me/theorems/9823b80b-6a2b-4c7b-8ce9-6712886fcca0
-- title:
--   Abstract Laminar: seam of adjacent
-- statement:
--   Distinct roots covering adjacent levels seam: if `r''` covers `s` and `r` covers a level just
--       above `s` (with `lo r < s+1`), and `r'' ≠ r`, then `hi r'' = lo r`.  (Used in the seam scan.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L234-L241
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L234-L241

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open AbstractLaminar
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)

theorem AbstractLaminar.seam_of_adjacent {a b : ℕ} {r'' r : ι} (hr'' : r'' ∈ Roots fam a b) (hr : r ∈ Roots fam a b)
    {s : ℕ} (hs1 : fam.lo r'' < s) (hs2 : s ≤ fam.hi r'')
    (hrhi : s + 1 ≤ fam.hi r) (hadj : fam.lo r = s) : fam.hi r'' = s := by sorry
