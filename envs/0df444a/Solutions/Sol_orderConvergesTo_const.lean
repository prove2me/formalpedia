-- Prove2me | solution 1 for orderConvergesTo_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:09.881815+00:00
-- url     : https://prove2.me/submissions/0aba5ad6-98bb-4964-9c0e-d9993808da24

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order

set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {ι : Type v} [Preorder ι]
     (x : X) :
    OrderConvergesTo (fun _ : ι => x) x := by
  refine ⟨ULift.{u} PUnit, inferInstance, inferInstance, inferInstance,
    fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    exact le_rfl
  · intro _
    exact le_rfl
  · simp
  · intro _
    filter_upwards with i
    simp
