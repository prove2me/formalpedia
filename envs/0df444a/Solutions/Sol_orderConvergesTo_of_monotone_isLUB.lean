-- Prove2me | solution 1 for orderConvergesTo_of_monotone_isLUB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:20.300953+00:00
-- url     : https://prove2.me/submissions/a9ae0ac5-b4b7-4e92-948b-753a1ea17217

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
section
@[expose] public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
omit [AddCommGroup X] [IsOrderedAddMonoid X] in
private theorem isDirected_range_monotone {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] {u : ι → X} (hmono : Monotone u) :
    IsDirected (Set.range u) (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  rcases a.2 with ⟨i, hi⟩
  rcases b.2 with ⟨j, hj⟩
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  exact ⟨⟨u k, ⟨k, rfl⟩⟩, by
    change (a : X) ≤ u k
    simpa [← hi] using hmono hik, by
    change (b : X) ≤ u k
    simpa [← hj] using hmono hjk⟩
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
    (hmono : Monotone u) (hlub : IsLUB (Set.range u) x) :
    OrderConvergesTo u x := by
  let : Nonempty (Set.range u) := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨⟨u i, ⟨i, rfl⟩⟩⟩
  refine ⟨Set.range u, inferInstance, isDirected_range_monotone hmono, inferInstance,
    fun y => x - y.1, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact sub_le_sub_left (show (a : X) ≤ (b : X) from h) x
  · rintro ⟨_, i, rfl⟩
    exact sub_nonneg.mpr (hlub.1 ⟨i, rfl⟩)
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨⟨_, i, rfl⟩, rfl⟩
      exact sub_nonneg.mpr (hlub.1 ⟨i, rfl⟩)
    · intro w hw
      have hlb : ∀ y ∈ Set.range u, y ≤ x - w := by
        rintro _ ⟨i, rfl⟩
        exact le_sub_comm.mp (hw ⟨⟨u i, ⟨i, rfl⟩⟩, rfl⟩)
      have h := hlub.2 hlb
      rwa [le_sub_iff_add_le, add_comm, add_le_iff_nonpos_left] at h
  · intro k
    rcases k.2 with ⟨j, hj⟩
    refine Filter.eventually_atTop.mpr ⟨j, fun i hij => ?_⟩
    have hix : u i ≤ x := hlub.1 ⟨i, rfl⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hix), neg_sub]
    simpa [hj] using sub_le_sub_left (hmono hij) x
