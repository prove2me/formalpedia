-- Prove2me | solution 1 for orderConvergesTo_of_antitone_isGLB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:13.344833+00:00
-- url     : https://prove2.me/submissions/3cb1e6fd-6be7-4c2a-9d36-228d6900e382

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
section
@[expose] public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
omit [AddCommGroup X] [IsOrderedAddMonoid X] in
private theorem isDirected_orderDual_range_antitone {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] {u : ι → X} (hanti : Antitone u) :
    IsDirected (OrderDual (Set.range u)) (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  rcases (OrderDual.ofDual a : Set.range u).2 with ⟨i, hi⟩
  rcases (OrderDual.ofDual b : Set.range u).2 with ⟨j, hj⟩
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  refine ⟨OrderDual.toDual (⟨u k, ⟨k, rfl⟩⟩ : Set.range u), ?_, ?_⟩
  · change (⟨u k, ⟨k, rfl⟩⟩ : Set.range u) ≤ OrderDual.ofDual a
    change u k ≤ (OrderDual.ofDual a : Set.range u)
    simpa [hi] using hanti hik
  · change (⟨u k, ⟨k, rfl⟩⟩ : Set.range u) ≤ OrderDual.ofDual b
    change u k ≤ (OrderDual.ofDual b : Set.range u)
    simpa [hj] using hanti hjk
namespace OrderConvergesTo
end OrderConvergesTo
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → X} {x : X}
    (hanti : Antitone u) (hglb : IsGLB (Set.range u) x) :
    OrderConvergesTo u x := by
  let : IsDirected (OrderDual (Set.range u)) (· ≤ ·) :=
    isDirected_orderDual_range_antitone hanti
  let : Nonempty (OrderDual (Set.range u)) := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨OrderDual.toDual (⟨u i, ⟨i, rfl⟩⟩ : Set.range u)⟩
  refine ⟨OrderDual (Set.range u), inferInstance, inferInstance, inferInstance,
    fun y => ((OrderDual.ofDual y : Set.range u) : X) - x, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact sub_le_sub_right (show ((OrderDual.ofDual b : Set.range u) : X) ≤
      ((OrderDual.ofDual a : Set.range u) : X) from hab) x
  · intro y
    exact sub_nonneg.mpr (hglb.1 (OrderDual.ofDual y).2)
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨y, rfl⟩
      exact sub_nonneg.mpr (hglb.1 (OrderDual.ofDual y).2)
    · intro w hw
      have hlb : ∀ y ∈ Set.range u, w + x ≤ y := by
        rintro _ ⟨i, rfl⟩
        exact add_le_of_le_sub_right
          (hw ⟨OrderDual.toDual (⟨u i, ⟨i, rfl⟩⟩ : Set.range u), rfl⟩)
      have h := hglb.2 hlb
      rwa [add_le_iff_nonpos_left] at h
  · intro y
    rcases (OrderDual.ofDual y : Set.range u).2 with ⟨j, hj⟩
    refine Filter.eventually_atTop.mpr ⟨j, fun i hij => ?_⟩
    have hxi : x ≤ u i := hglb.1 ⟨i, rfl⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hxi)]
    simpa [hj] using sub_le_sub_right (hanti hij) x
