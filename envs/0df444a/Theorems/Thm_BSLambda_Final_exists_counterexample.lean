-- Prove2me | Theorems.Thm_BSLambda_Final_exists_counterexample
-- name    : BSLambda.Final.exists_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:40:44.724812+00:00
-- url     : https://prove2.me/theorems/99d46d2f-c26d-49cd-9a75-46b35820e601
-- title:
--   Final: exists counterexample
-- statement:
--   **The counterexample** (Sections 5 and 12).  There is a total Boolean function `f`
--   with `bs(f) ≥ 14011` and `lambda(f)^2 ≤ U = 7149 + 2 √150108 < 7924`; since
--   `α = 2 log 14011 / log U > 2`, it also satisfies `lambda(f)^α ≤ bs(f)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L305-L310
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L305-L310

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

theorem BSLambda.Final.exists_counterexample :
    ∃ γ : Idx → Idx → Fin r,
      14011 ≤ bs (ind Arc γ) ∧ lam (ind Arc γ) ^ 2 ≤ U ∧
        lam (ind Arc γ) ^ alpha ≤ (bs (ind Arc γ) : ℝ) := by sorry
