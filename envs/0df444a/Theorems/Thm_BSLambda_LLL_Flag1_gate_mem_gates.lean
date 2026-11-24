-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_gate_mem_gates
-- name    : BSLambda.LLL.Flag1.gate_mem_gates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:39.060203+00:00
-- url     : https://prove2.me/theorems/6dc84e79-aac7-4347-8ce8-7f9c8bba8187
-- title:
--   Flag1: gate mem gates
-- statement:
--   The owner gate into the head block of an internal arc is one of the conditioned
--   gates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L537-L540
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L537-L540

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

theorem BSLambda.LLL.Flag1.gate_mem_gates (F : Flag1 ι) {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    (hF : F.Active Arc) {p : ι × ι} (hp : p ∈ arcSet Arc F.nonOwners) :
    (F.owner, p.2) ∈ ownerGates F.owner F.bot := by sorry
