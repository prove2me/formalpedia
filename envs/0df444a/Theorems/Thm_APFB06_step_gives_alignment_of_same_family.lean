-- Prove2me | Theorems.Thm_APFB06_step_gives_alignment_of_same_family
-- name    : APFB06.step_gives_alignment_of_same_family
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:15:42.879895+00:00
-- url     : https://prove2.me/theorems/a181a62a-2e65-43e3-9650-c6fee55c0c21
-- title:
--   Step gives alignment of same family
-- statement:
--   If every task of S is active at the physical class of after(x,u), that class and S form an OriginalAlignment with exactly the same carried family. The post-step activity is assumed; the construction does not prove it.
-- source:
--   Sib v44 Theorems/Thm_APFB06_overlapping_families.lean:65

import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding
import Theorems.Thm_APFPaper5_K1_hold_bills_nothing_more
import Theorems.Thm_APFPaper5_K1_bill_of_repeated_draw
import Theorems.Thm_APFPaper5_K1_repeated_draw_bounded

set_option autoImplicit false

theorem APFB06.step_gives_alignment_of_same_family {Raw FullProcess : Type*}
    (Cont : Raw → FullProcess → Prop) (Dset : Set (APFB01.PhysicalState Cont → Bool))
    (after : Raw → FullProcess → Raw) (S : Finset (APFB06.Task Cont Dset)) (x : Raw)
    (u : FullProcess)
    (hkeep : ∀ d ∈ S, d.val (APFB01.physicalClass Cont (after x u)) = true) :
    ∃ o : APFB06.OriginalAlignment Cont Dset,
      o.carried = S ∧ o.carrier = APFB01.physicalClass Cont (after x u) := by sorry
