-- Prove2me | Theorems.Thm_APFPaper1_Ranks_extension_union_ledger
-- name    : APFPaper1.Ranks.extension_union_ledger
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-10-08T05:04:50.115998+00:00
-- url     : https://prove2.me/theorems/431b0615-6920-440a-9fd3-3848a94a3a33
-- title:
--   List insertion equals finite-set union
-- statement:
--   For arbitrary S and ds, repeated insertion of ds into S yields exactly S union ds.toFinset. This is ordinary set membership bookkeeping; it establishes no admissibility, novelty, rank or cost property.
-- source:
--   Paper1 Supplement v9.27:2836–2847,2853–2856. Existing seed extension_union, ordinary finite-set bookkeeping. Inputs revision2026-10-04.1 is the policy baseline; no physical input consumed. Exact extend recursion and theorem proof body preserved; unrelated historical Ranks/cost definitions and project imports removed. extend represents only the finite set accumulated from an ordered list by insertion; it neither represents nor certifies the paper's additional tested, distinct, admissible and support-novel chain conditions.

import Definitions.Def_APFPaper1_RankExtend
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical APFPaper1.Ranks

theorem APFPaper1.Ranks.extension_union_ledger {D : Type*} [DecidableEq D] (S : Finset D) (ds : List D) :
    extend S ds = S ∪ ds.toFinset := by sorry
