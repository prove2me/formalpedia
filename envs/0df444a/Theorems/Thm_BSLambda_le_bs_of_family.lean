-- Prove2me | Theorems.Thm_BSLambda_le_bs_of_family
-- name    : BSLambda.le_bs_of_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:53.902882+00:00
-- url     : https://prove2.me/theorems/660d2149-5a07-4b83-bb4d-34435ca15a10
-- title:
--   BSLambda: le bs of family
-- statement:
--   The main lower-bound interface for block sensitivity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L132-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L132-L134

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.le_bs_of_family {f : Input V → Bool} {x : Input V} {𝓑 : Finset (Finset V)}
    (h : IsBlockFamily f x 𝓑) : 𝓑.card ≤ bs f := by sorry
