-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_mem_offDiag_supp
-- name    : BSLambda.LLL.Flag1.mem_offDiag_supp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:41.495798+00:00
-- url     : https://prove2.me/theorems/7b2f3b63-472c-49ad-9c0f-591734e9caa3
-- title:
--   Flag1: mem off Diag supp
-- statement:
--   Both variables read by the flag event at an internal arc are variables of its support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L506-L513
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L506-L513

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

theorem BSLambda.LLL.Flag1.mem_offDiag_supp {Arc : ι → ι → Bool} (hT : IsTournament Arc) {F : Flag1 ι}
    (hF : F.Active Arc) {p : ι × ι} (hp : p ∈ arcSet Arc F.nonOwners) :
    p ∈ F.supp.offDiag ∧ (F.owner, p.2) ∈ F.supp.offDiag := by sorry
