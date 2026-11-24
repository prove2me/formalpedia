-- Prove2me | Theorems.Thm_Finset_symmDiff_singleton_singleton
-- name    : Finset.symmDiff_singleton_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:15.561847+00:00
-- url     : https://prove2.me/theorems/6ebff986-8311-418c-8e1b-bfb505e2cab3
-- title:
--   Finset: symm Diff singleton singleton
-- statement:
--   The symmetric difference of two distinct singletons is the corresponding pair.  This is a
--   general `Finset` fact, stated here because Mathlib does not have it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L27-L30
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L27-L30

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section

theorem Finset.symmDiff_singleton_singleton {α : Type*} [DecidableEq α] {p q : α} (hpq : p ≠ q) :
    symmDiff ({p} : Finset α) {q} = {p, q} := by sorry
