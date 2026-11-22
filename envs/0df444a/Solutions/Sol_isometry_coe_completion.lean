-- Prove2me | solution 1 for isometry_coe_completion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:23.82+00:00
-- url     : https://prove2.me/submissions/cb356222-7149-4034-a492-42ddcbd28ab3

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed

set_option autoImplicit true
@[expose] public section
public section
open UniformSpace
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
theorem _root_.solution : Isometry ((↑) : X → Completion X) := by
  rw [← Completion.coe_toComplₗᵢ (𝕜 := ℝ)]
  exact (Completion.toComplₗᵢ (𝕜 := ℝ)).isometry
