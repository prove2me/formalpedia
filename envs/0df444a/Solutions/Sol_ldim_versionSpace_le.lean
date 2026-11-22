-- Prove2me | solution 1 for ldim_versionSpace_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:21.059304+00:00
-- url     : https://prove2.me/submissions/bfcdd2fe-732c-4f21-93cd-4eced1e66169

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
public import Theorems.Thm_LTree_isShattered_mono
public import Theorems.Thm_versionSpace_subset

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} :
    LittlestoneDim X (versionSpace C history) ≤ LittlestoneDim X C := by
  apply iSup₂_le; intro n ⟨T, hT⟩
  exact le_iSup₂_of_le n ⟨T, T.isShattered_mono versionSpace_subset hT⟩ le_rfl
