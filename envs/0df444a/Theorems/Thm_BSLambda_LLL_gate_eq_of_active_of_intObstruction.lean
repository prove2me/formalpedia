-- Prove2me | Theorems.Thm_BSLambda_LLL_gate_eq_of_active_of_intObstruction
-- name    : BSLambda.LLL.gate_eq_of_active_of_intObstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:04.233795+00:00
-- url     : https://prove2.me/theorems/af5c17dd-abc3-40d9-9f6a-c94a49ab64df
-- title:
--   LLL: gate eq of active of int Obstruction
-- statement:
--   **Section 8**: all internal arcs of the flag produced from a radius-one obstruction
--   carry the owner's gate label.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L728-L744
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L728-L744

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

theorem BSLambda.LLL.gate_eq_of_active_of_intObstruction {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) {F : Flag1 ι} (hF : F.Active Arc)
    (hsupp : F.supp = S) (hFh : F.owner = h) :
    ∀ p ∈ arcSet Arc F.nonOwners, γ p.1 p.2 = γ h p.2 := by sorry
