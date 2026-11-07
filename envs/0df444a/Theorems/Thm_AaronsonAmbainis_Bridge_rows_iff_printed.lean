-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_rows_iff_printed
-- name    : AaronsonAmbainis.Bridge.rows_iff_printed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:07.393551+00:00
-- url     : https://prove2.me/theorems/c55cd94b-3412-4c01-9752-4d6000898054
-- title:
--   Bridge: rows iff printed
-- statement:
--   Rows of cost at most `K` in the two forms: a family `a` with
--   `|f(x) − f(y)| ≤ ∑_{j ∈ Δ(x,y)} a x j` for all `x, y`, as in the propositions of
--   `Statements.lean`; and, for every `x`, a vector `a ∈ [0,∞)^n` with `‖a‖ ≤ K` and
--   `|f(x) − f(x^S)| ≤ a(S)` for every `S ⊆ [n]`, as in Definition 2.3 of the paper.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperTheorems.lean#L51-L67
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperTheorems.lean#L51-L67

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.rows_iff_printed (f : Cube ι → ℝ) (K : ℝ) :
    (∃ a : Cube ι → ι → ℝ, (∀ x j, 0 ≤ a x j) ∧ (∀ x, ∑ j, a x j ≤ K) ∧
        ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) ↔
      ∀ x : Cube ι, ∃ a : ι → ℝ, (∀ j, 0 ≤ a j) ∧ ∑ j, a j ≤ K ∧
        ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ j ∈ S, a j := by sorry
