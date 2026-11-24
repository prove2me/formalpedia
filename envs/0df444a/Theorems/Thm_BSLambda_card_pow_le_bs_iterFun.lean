-- Prove2me | Theorems.Thm_BSLambda_card_pow_le_bs_iterFun
-- name    : BSLambda.card_pow_le_bs_iterFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:57.165189+00:00
-- url     : https://prove2.me/theorems/b2da0c33-a66e-4c00-846e-93c3573da440
-- title:
--   BSLambda: card pow le bs iter Fun
-- statement:
--   **Section 14**: the `k^m` Cartesian-product blocks are pairwise disjoint sensitive
--   blocks of `F_m` at the all-zero input, so `bs(F_m) ≥ k^m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L180-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L180-L191

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u

theorem BSLambda.card_pow_le_bs_iterFun {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    {f : Input V → Bool} {blk : ι → Finset V}
    (hzero : f (zeroInput V) = false)
    (hflip : ∀ i, f (flipSet (zeroInput V) (blk i)) = true)
    (hne : ∀ i, (blk i).Nonempty)
    (hdisj : Pairwise (Disjoint on blk)) (m : ℕ) :
    Fintype.card ι ^ m ≤ bs (iterFun f m) := by sorry
