-- Prove2me | Theorems.Thm_BSLambda_Final_bs_iter_ge
-- name    : BSLambda.Final.bs_iter_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:02.849265+00:00
-- url     : https://prove2.me/theorems/c0517d91-2aa2-4c2c-95cf-abed9d5fb998
-- title:
--   Final: bs iter ge
-- statement:
--   **Block sensitivity of the iterates** (Section 14): `bs(F_m) ≥ 14011 ^ m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L212-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L212-L216

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}

theorem BSLambda.Final.bs_iter_ge (m : ℕ) : 14011 ^ m ≤ bs (iterFun (ind Arc γ) m) := by sorry
