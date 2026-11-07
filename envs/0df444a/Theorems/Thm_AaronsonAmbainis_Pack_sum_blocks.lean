-- Prove2me | Theorems.Thm_AaronsonAmbainis_Pack_sum_blocks
-- name    : AaronsonAmbainis.Pack.sum_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:40:48.869206+00:00
-- url     : https://prove2.me/theorems/b0b952ef-a507-4964-9487-62e66fa01979
-- title:
--   Pack: sum blocks
-- statement:
--   A sum over the family `Σ S, Fin (k S)` of a function of the block.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Blocks.lean#L32-L37
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Blocks.lean#L32-L37

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Pack_Blocks
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Pack.sum_blocks (k : Finset ι → ℕ) (g : Finset ι → ℝ) :
    ∑ b : (Σ S : Finset ι, Fin (k S)), g b.1 = ∑ S, (k S : ℝ) * g S := by sorry
