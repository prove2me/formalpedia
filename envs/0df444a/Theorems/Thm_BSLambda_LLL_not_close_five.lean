-- Prove2me | Theorems.Thm_BSLambda_LLL_not_close_five
-- name    : BSLambda.LLL.not_close_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:58.034301+00:00
-- url     : https://prove2.me/theorems/f3028509-8d70-45ca-844f-5ef9f8104f32
-- title:
--   LLL: not close five
-- statement:
--   **Section 10.3**: a positive point of `C_h` cannot have four further certificates of a
--   five-element support at distance at most one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L823-L828
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L823-L828

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}

theorem BSLambda.LLL.not_close_five (hT : IsTournament Arc) {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) {S : Finset ι} (hS : S.card = 5)
    {h : ι} (hh : h ∈ S) {x : Input (Coord ι r)}
    (hx : (cert Arc (toGamma ω) h).Sat x)
    (hclose : ∀ i ∈ S, i ≠ h → (cert Arc (toGamma ω) i).dist x ≤ 1) : False := by sorry
