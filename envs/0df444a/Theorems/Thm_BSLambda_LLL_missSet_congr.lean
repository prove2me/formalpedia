-- Prove2me | Theorems.Thm_BSLambda_LLL_missSet_congr
-- name    : BSLambda.LLL.missSet_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:11.708604+00:00
-- url     : https://prove2.me/theorems/89ca970d-2bdc-4212-ba4a-aeeb5f320ada
-- title:
--   LLL: miss Set congr
-- statement:
--   The misses out of `i` only read gate labels of arcs with both endpoints in `S`, so they
--   are unchanged by a relabelling that fixes those arcs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L181-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L181-L187

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
variable {Arc : ι → ι → Bool} {γ γ' : ι → ι → Fin r} {Z : ι → Finset (Fin r)}
  {T T' S : Finset ι} {i j : ι}

theorem BSLambda.LLL.missSet_congr (hT : IsTournament Arc) (hi : i ∈ S) (Z : ι → Finset (Fin r))
    (hagree : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → γ a b = γ' a b) :
    missSet Arc γ Z S i = missSet Arc γ' Z S i := by sorry
