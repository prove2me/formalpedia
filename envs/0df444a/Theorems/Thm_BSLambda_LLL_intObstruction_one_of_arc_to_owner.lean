-- Prove2me | Theorems.Thm_BSLambda_LLL_intObstruction_one_of_arc_to_owner
-- name    : BSLambda.LLL.intObstruction_one_of_arc_to_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:42.234812+00:00
-- url     : https://prove2.me/theorems/034e976a-326e-43af-bbf1-a70a5025db8a
-- title:
--   LLL: int Obstruction one of arc to owner
-- statement:
--   Under a radius-one obstruction centred at `h`, a vertex `j` that beats `h` already
--   spends its whole budget on the miss `j → h`, so `Z j = ∅` and it has no other miss.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L604-L614
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L604-L614

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

theorem BSLambda.LLL.intObstruction_one_of_arc_to_owner {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}
    {S : Finset ι} {h : ι} (hh : h ∈ S) {Z : ι → Finset (Fin r)} (hZh : Z h = ∅)
    (hbud : ∀ i ∈ S, i ≠ h → (Z i).card + (missSet Arc γ Z S i).card ≤ 1)
    {j : ι} (hj : j ∈ S) (hjh : j ≠ h) (harc : Arc j h = true) :
    Z j = ∅ ∧ ∀ k ∈ S, k ≠ h → Arc j k = true → γ j k ∈ Z k := by sorry
