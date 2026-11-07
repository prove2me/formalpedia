-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_disjoint_blocks_of_block
-- name    : AaronsonAmbainis.Row.disjoint_blocks_of_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:26.983084+00:00
-- url     : https://prove2.me/theorems/229d9108-0c4e-4890-999d-f4769e4262af
-- title:
--   Row: disjoint blocks of block
-- statement:
--   For pairwise disjoint blocks `S b`, `∑_b |f(x) - f(x^{S b})| ≤ 4 d²`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/DisjointBlocks.lean#L20-L36
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/DisjointBlocks.lean#L20-L36

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_DisjointBlocks
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Row

theorem AaronsonAmbainis.Row.disjoint_blocks_of_block (hBlock : BlockInequality) (ι : Type) [Fintype ι]
    [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hdeg : HasDegreeLE f d)
    (x : Cube ι) (β : Type) [Fintype β] (S : β → Finset ι)
    (hS : ∀ b b' : β, b ≠ b' → Disjoint (S b) (S b')) :
    ∑ b, |f x - f (flipSet x (S b))| ≤ 4 * (d : ℝ) ^ 2 := by sorry
