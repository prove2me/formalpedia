-- Prove2me | Theorems.Thm_BSLambda_LLL_intObstruction_congr
-- name    : BSLambda.LLL.intObstruction_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:17.765203+00:00
-- url     : https://prove2.me/theorems/843debd5-e640-4093-95e8-b6f0aebefeb4
-- title:
--   LLL: int Obstruction congr
-- statement:
--   A centered internal obstruction only reads gate labels of arcs with both endpoints in
--   its support, so it transports along any relabelling that fixes those arcs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L206-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L206-L215

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

theorem BSLambda.LLL.intObstruction_congr {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {ell : ℕ} {S : Finset ι} {h : ι} (hh : h ∈ S) {γ γ' : ι → ι → Fin r}
    (hagree : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → γ a b = γ' a b)
    (hobs : IntObstruction Arc ell S h γ) : IntObstruction Arc ell S h γ' := by sorry
