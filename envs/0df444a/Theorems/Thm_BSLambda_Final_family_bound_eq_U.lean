-- Prove2me | Theorems.Thm_BSLambda_Final_family_bound_eq_U
-- name    : BSLambda.Final.family_bound_eq_U
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:44.035358+00:00
-- url     : https://prove2.me/theorems/9f61e27d-c3d1-485c-a300-1ad24542e2c8
-- title:
--   Final: family bound eq U
-- statement:
--   Substituting `c = 7149`, `A = 3`, `B = 7` into the Spectral Lemma's right-hand side
--   `c + 2 √(A (c-1) B)` gives exactly `U = 7149 + 2 √150108` (Section 12).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L145-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L145-L148

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

theorem BSLambda.Final.family_bound_eq_U (h₁ : ListOne γ) (h₂ : ListTwo γ) :
    ((family γ h₁ h₂).c : ℝ) + 2 * (family γ h₁ h₂).offBound = U := by sorry
