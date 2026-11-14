-- Prove2me | Theorems.Thm_APFPaper5_K1_interchangeable_posDef
-- name    : APFPaper5.K1.interchangeable_posDef
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:32:36.594179+00:00
-- url     : https://prove2.me/theorems/43195943-08a8-4f80-a497-ef6d59375c5c
-- title:
--   Interchangeable tables with 0≤c<1 have faithful nonnegative diagonals
-- statement:
--   Let G be a real table on a finite index set. Assume hG: its diagonal entries are one and all off-diagonal entries equal c, together with h0: c≥0 and h1: c<1. Then its coefficient form F has F(x,x)≥0 for every x, and F(x,x)=0 implies x=0. These are sufficient conditions on a supplied table. The theorem does not identify it with a physical score, construct boundary classes, or establish that any interface has interchangeable marks.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_mark_table.lean:63; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-391;3038-3041

import Definitions.Def_APFPaper5_K1_MarkTable
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u
variable {ι : Type u} [Fintype ι]

theorem APFPaper5.K1.interchangeable_posDef [DecidableEq ι] (G : ι → ι → ℝ) (c : ℝ)
    (hG : Interchangeable G c) (h0 : 0 ≤ c) (h1 : c < 1) (x : ι → ℝ) :
    0 ≤ tableForm G x x ∧ (tableForm G x x = 0 → x = 0) := by sorry
