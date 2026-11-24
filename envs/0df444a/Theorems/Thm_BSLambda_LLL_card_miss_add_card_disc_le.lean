-- Prove2me | Theorems.Thm_BSLambda_LLL_card_miss_add_card_disc_le
-- name    : BSLambda.LLL.card_miss_add_card_disc_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:38.244442+00:00
-- url     : https://prove2.me/theorems/2ff688c7-9227-4012-9730-e1df2b799f84
-- title:
--   LLL: card miss add card disc le
-- statement:
--   **Section 9**: if `l` non-owners take a discretionary zero, the total number of misses
--   among the twenty-eight internal non-owner arcs is at most `8 - l`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L985-L998
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L985-L998

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
omit [Fintype ι]

theorem BSLambda.LLL.card_miss_add_card_disc_le [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι} (hh : h ∈ S)
    {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} (hZh : Z h = ∅)
    (hgate : ∀ j ∈ S, Arc h j → γ h j ∈ Z j)
    (hbud : ∀ i ∈ S, i ≠ h → (Z i).card + (missSet Arc γ Z S i).card ≤ 2) :
    (missArcs Arc γ Z (S.erase h)).card + (discSet γ Z (S.erase h) h).card ≤ 8 := by sorry
