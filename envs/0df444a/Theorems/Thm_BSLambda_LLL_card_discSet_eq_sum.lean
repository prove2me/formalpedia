-- Prove2me | Theorems.Thm_BSLambda_LLL_card_discSet_eq_sum
-- name    : BSLambda.LLL.card_discSet_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:21.956038+00:00
-- url     : https://prove2.me/theorems/b71c03e5-4fa1-4e45-b28b-00db5057b3ce
-- title:
--   LLL: card disc Set eq sum
-- statement:
--   The discretionary vertices are counted by their indicator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L850-L853
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L850-L853

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
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} {T : Finset ι}
  {p : ι × ι}
omit [DecidableEq ι]

theorem BSLambda.LLL.card_discSet_eq_sum (T : Finset ι) (h : ι) :
    (discSet γ Z T h).card = ∑ j ∈ T, if Z j ⊆ {γ h j} then 0 else 1 := by sorry
