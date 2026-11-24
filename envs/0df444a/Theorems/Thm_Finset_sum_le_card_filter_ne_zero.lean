-- Prove2me | Theorems.Thm_Finset_sum_le_card_filter_ne_zero
-- name    : Finset.sum_le_card_filter_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:45.532964+00:00
-- url     : https://prove2.me/theorems/5669654e-f665-4406-a567-34b68127cd26
-- title:
--   Finset: sum le card filter ne zero
-- statement:
--   A finite sum of reals that are each at most one is at most the number of nonzero terms.
--   This is a general `Finset` fact, stated here because Mathlib does not have it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L42-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L42-L45

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
set_option autoImplicit true
@[expose] public section
public section

theorem Finset.sum_le_card_filter_ne_zero {α : Type*} (s : Finset α) {f : α → ℝ}
    (hf : ∀ a ∈ s, f a ≤ 1) : ∑ a ∈ s, f a ≤ ((s.filter fun a ↦ f a ≠ 0).card : ℝ) := by sorry
