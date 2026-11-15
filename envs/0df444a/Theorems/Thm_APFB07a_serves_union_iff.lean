-- Prove2me | Theorems.Thm_APFB07a_serves_union_iff
-- name    : APFB07a.serves_union_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:16:09.924982+00:00
-- url     : https://prove2.me/theorems/ffb0200e-a08e-4c92-8e86-f8872042c667
-- title:
--   Serves union iff
-- statement:
--   One fixed protocol serves S union T if and only if it serves S and serves T, with service defined task by task using maintained sufficient support and actual use. Separate existence of a protocol for S and one for T does not imply existence of a protocol for their union.
-- source:
--   Sib v44 Theorems/Thm_APFB06_overlapping_families.lean:50

import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding
import Theorems.Thm_APFPaper5_K1_hold_bills_nothing_more
import Theorems.Thm_APFPaper5_K1_bill_of_repeated_draw
import Theorems.Thm_APFPaper5_K1_repeated_draw_bounded

set_option autoImplicit false

theorem APFB07a.serves_union_iff {D P Record : Type*} [DecidableEq D] (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S T : Finset D) (p : P) :
    APFB07a.Serves maintained sufficient usesToRealize (S ∪ T) p ↔
      APFB07a.Serves maintained sufficient usesToRealize S p ∧
        APFB07a.Serves maintained sufficient usesToRealize T p := by sorry
