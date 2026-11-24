-- Prove2me | Theorems.Thm_BSLambda_LLL_card_arcSet_swap
-- name    : BSLambda.LLL.card_arcSet_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:05:32.451881+00:00
-- url     : https://prove2.me/theorems/8e6366f6-d561-4757-b841-40c2a673dde8
-- title:
--   LLL: card arc Set swap
-- statement:
--   Swapping the two entries is a bijection from the arcs of `T` to the reversed arcs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L107-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L107-L116

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
variable {Arc : ι → ι → Bool} {T : Finset ι} {p : ι × ι}
omit [DecidableEq ι]

theorem BSLambda.LLL.card_arcSet_swap (Arc : ι → ι → Bool) (T : Finset ι) :
    (arcSet (fun a b => Arc b a) T).card = (arcSet Arc T).card := by sorry
