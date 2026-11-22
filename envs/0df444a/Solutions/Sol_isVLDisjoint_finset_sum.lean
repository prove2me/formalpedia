-- Prove2me | solution 1 for isVLDisjoint_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:56.96839+00:00
-- url     : https://prove2.me/submissions/7303391b-7719-46b8-9f88-39605eb0d711

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_isVLDisjoint_zero_right
public import Theorems.Thm_IsVLDisjoint_add_right

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {ι : Type*} {s : Finset ι} {x : X} {f : ι → X}
    (h : ∀ i ∈ s, IsVLDisjoint x (f i)) : IsVLDisjoint x (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isVLDisjoint_zero_right x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (h a (Finset.mem_insert_self a s)).add_right ?_
    exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
