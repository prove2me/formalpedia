-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_disjoint_gates_arcs
-- name    : BSLambda.LLL.Flag1.disjoint_gates_arcs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:43.261289+00:00
-- url     : https://prove2.me/theorems/585833af-763b-47ee-99e5-d6666a468c6c
-- title:
--   Flag1: disjoint gates arcs
-- statement:
--   The owner gates conditioned on in Section 8.1 are disjoint from the internal arcs, so
--   the two families of variables are independent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L528-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L528-L532

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

theorem BSLambda.LLL.Flag1.disjoint_gates_arcs (F : Flag1 ι) {Arc : ι → ι → Bool} (hF : F.Active Arc) :
    Disjoint (ownerGates F.owner F.bot) (arcSet Arc F.nonOwners) := by sorry
