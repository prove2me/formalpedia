-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_active_iff_of_top_eq_none
-- name    : BSLambda.LLL.Flag1.active_iff_of_top_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:19.671806+00:00
-- url     : https://prove2.me/theorems/fe4abce9-bb1d-4cd6-9619-c47d07d76f46
-- title:
--   Flag1: active iff of top eq none
-- statement:
--   Activeness of a `Type A` flag: the owner dominates its four bottom vertices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L398-L400
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L398-L400

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

theorem BSLambda.LLL.Flag1.active_iff_of_top_eq_none (ha : F.top = none) :
    F.Active Arc ↔ F.owner ∉ F.bot ∧ F.bot.card = 4 ∧ ∀ j ∈ F.bot, Arc F.owner j = true := by sorry
