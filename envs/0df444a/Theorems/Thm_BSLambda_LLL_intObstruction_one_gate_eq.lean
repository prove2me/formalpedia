-- Prove2me | Theorems.Thm_BSLambda_LLL_intObstruction_one_gate_eq
-- name    : BSLambda.LLL.intObstruction_one_gate_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:58.889891+00:00
-- url     : https://prove2.me/theorems/14d3f424-87e3-4b65-9264-36ed81703d6a
-- title:
--   LLL: int Obstruction one gate eq
-- statement:
--   **Section 8**: every non-owner arc into a dominated `j` carries the owner's label,
--   since `Z j` is the singleton `{γ h j}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L677-L690
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L677-L690

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

theorem BSLambda.LLL.intObstruction_one_gate_eq {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) {i j : ι} (hi : i ∈ S) (hj : j ∈ S)
    (hih : i ≠ h) (hjh : j ≠ h) (harc : Arc i j = true) (hhj : Arc h j = true) :
    γ i j = γ h j := by sorry
