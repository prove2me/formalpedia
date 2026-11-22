-- Prove2me | solution 1 for nonneg_and_nonneg_of_isVLDisjoint_add_eq_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:24.706649+00:00
-- url     : https://prove2.me/submissions/6caa649b-1255-44e7-a08d-f6adb17a9a62

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_abs_add_of_isVLDisjoint

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution
    {x y z : X} (hx : 0 ≤ x) (hyz : IsVLDisjoint y z) (hadd : y + z = x) :
    0 ≤ y ∧ 0 ≤ z := by
  have hsub : |y| + |z| - (y + z) = 0 := by
    calc
      |y| + |z| - (y + z) = |y + z| - (y + z) := by
        rw [abs_add_of_isVLDisjoint hyz]
      _ = |x| - x := by rw [hadd]
      _ = 0 := by rw [abs_of_nonneg hx, sub_self]
  have hy0 : |y| - y = 0 := by
    have hle : |y| - y ≤ |y| + |z| - (y + z) := by
      calc
        |y| - y ≤ (|y| - y) + (|z| - z) :=
          le_add_of_nonneg_right (sub_nonneg.mpr (le_abs_self z))
        _ = |y| + |z| - (y + z) := by abel
    exact le_antisymm (by rwa [hsub] at hle) (sub_nonneg.mpr (le_abs_self y))
  have hz0 : |z| - z = 0 := by
    calc
      |z| - z = 0 + (|z| - z) := by rw [zero_add]
      _ = (|y| - y) + (|z| - z) := by rw [hy0]
      _ = |y| + |z| - (y + z) := by abel
      _ = 0 := hsub
  constructor
  · rw [← sub_eq_zero.mp hy0]
    exact abs_nonneg y
  · rw [← sub_eq_zero.mp hz0]
    exact abs_nonneg z
