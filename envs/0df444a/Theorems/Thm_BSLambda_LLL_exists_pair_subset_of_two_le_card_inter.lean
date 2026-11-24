-- Prove2me | Theorems.Thm_BSLambda_LLL_exists_pair_subset_of_two_le_card_inter
-- name    : BSLambda.LLL.exists_pair_subset_of_two_le_card_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:02.840393+00:00
-- url     : https://prove2.me/theorems/7cf677ed-054b-4db9-a8b3-ec276bee7e68
-- title:
--   LLL: exists pair subset of two le card inter
-- statement:
--   Two vertices shared between `V` and `W` yield a two-element subset of `V` contained in
--   `W`.  This is what turns `two_le_card_inter_of_mem_nbr` into "the neighbour's support
--   contains one of the `C(|V|,2)` pairs of `V`" (Section 10.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L150-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L150-L155

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
omit [Fintype ι]

theorem BSLambda.LLL.exists_pair_subset_of_two_le_card_inter {V W : Finset ι}
    (h : 2 ≤ (V ∩ W).card) : ∃ p ∈ V.powersetCard 2, p ⊆ W := by sorry
