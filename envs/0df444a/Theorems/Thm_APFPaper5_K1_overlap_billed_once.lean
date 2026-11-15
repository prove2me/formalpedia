-- Prove2me | Theorems.Thm_APFPaper5_K1_overlap_billed_once
-- name    : APFPaper5.K1.overlap_billed_once
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:19:36.81021+00:00
-- url     : https://prove2.me/theorems/64f8d145-7df9-46f2-bfed-59d1426556df
-- title:
--   Overlap billed once
-- statement:
--   For nonnegative real record weights and finite record sets K,L, the sum on their union is at most the sum on K plus the sum on L. This is finite weighted-set accounting, not a theorem that arbitrary joint protocol costs are subadditive.
-- source:
--   Sib v44 Theorems/Thm_APFB06_overlapping_families.lean:89

import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding
import Theorems.Thm_APFPaper5_K1_hold_bills_nothing_more
import Theorems.Thm_APFPaper5_K1_bill_of_repeated_draw
import Theorems.Thm_APFPaper5_K1_repeated_draw_bounded

set_option autoImplicit false











namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1

theorem APFPaper5.K1.overlap_billed_once {Rec : Type*} [DecidableEq Rec] (w : Rec → ℝ)
    (hw : ∀ r : Rec, 0 ≤ w r) (K L : Finset Rec) :
    ∑ r ∈ K ∪ L, w r ≤ ∑ r ∈ K, w r + ∑ r ∈ L, w r := by sorry
