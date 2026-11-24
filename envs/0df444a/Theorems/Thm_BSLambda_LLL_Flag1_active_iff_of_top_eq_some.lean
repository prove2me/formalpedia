-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_active_iff_of_top_eq_some
-- name    : BSLambda.LLL.Flag1.active_iff_of_top_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:00:08.433815+00:00
-- url     : https://prove2.me/theorems/92c4ab74-5e60-43f1-aa0e-0f56fdec8d2d
-- title:
--   Flag1: active iff of top eq some
-- statement:
--   Activeness of a `Type B` flag: the owner, the second top vertex `a` and the three bottom
--   vertices are distinct, `a` beats the owner, and both top vertices dominate every bottom
--   vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L405-L408
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L405-L408

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
open BSLambda.LLL.Flag1
omit [Fintype ι]
variable {F : Flag1 ι} {Arc : ι → ι → Bool} {a j : ι} {p : ι × ι}

theorem BSLambda.LLL.Flag1.active_iff_of_top_eq_some (ha : F.top = some a) :
    F.Active Arc ↔ F.owner ≠ a ∧ F.owner ∉ F.bot ∧ a ∉ F.bot ∧ F.bot.card = 3 ∧
      Arc a F.owner = true ∧ ∀ j ∈ F.bot, Arc F.owner j = true ∧ Arc a j = true := by sorry
