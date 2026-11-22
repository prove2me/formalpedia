-- Prove2me | solution 1 for le_of_orderConvergesTo_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:17.721605+00:00
-- url     : https://prove2.me/submissions/44bc233f-f8af-4e76-b07c-69140827974f

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Theorems.Thm_OrderConvergesTo_le_of_forall_le

set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → X} {x b : X}
    (hu : OrderConvergesTo u x) (hub : ∀ i, u i ≤ b) :
    x ≤ b :=
  hu.le_of_forall_le hub
