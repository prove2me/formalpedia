-- Prove2me | Theorems.Thm_BSLambda_LLL_intObstruction_one_of_owner_arc
-- name    : BSLambda.LLL.intObstruction_one_of_owner_arc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:24.319194+00:00
-- url     : https://prove2.me/theorems/3b2b6b68-512b-4be8-be32-332341c10a5d
-- title:
--   LLL: int Obstruction one of owner arc
-- statement:
--   Under a radius-one obstruction centred at `h`, a vertex `j` dominated by `h` has its
--   zero set pinned to the single owner gate `γ h j`, and hence no internal miss of its own.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L583-L599
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L583-L599

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem BSLambda.LLL.intObstruction_one_of_owner_arc {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}
    {S : Finset ι} {h : ι} {Z : ι → Finset (Fin r)}
    (hgate : ∀ j ∈ S, Arc h j → γ h j ∈ Z j)
    (hbud : ∀ i ∈ S, i ≠ h → (Z i).card + (missSet Arc γ Z S i).card ≤ 1)
    {j : ι} (hj : j ∈ S) (hjh : j ≠ h) (harc : Arc h j = true) :
    Z j = {γ h j} ∧ ∀ k ∈ S, Arc j k = true → γ j k ∈ Z k := by sorry
