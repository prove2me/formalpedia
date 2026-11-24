-- Prove2me | Theorems.Thm_BSLambda_LLL_intObstruction_one_card_beats_le_one
-- name    : BSLambda.LLL.intObstruction_one_card_beats_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:55.245251+00:00
-- url     : https://prove2.me/theorems/f22e2bfa-1f78-428a-a995-ca89f412eaee
-- title:
--   LLL: int Obstruction one card beats le one
-- statement:
--   **Section 8**: at most one vertex of the support beats the centre `h`; two of them
--   would give one a second internal miss.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L619-L639
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L619-L639

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

theorem BSLambda.LLL.intObstruction_one_card_beats_le_one {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) :
    (S.filter fun j => Arc j h = true).card ≤ 1 := by sorry
