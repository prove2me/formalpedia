-- Prove2me | Theorems.Thm_BSLambda_Construction_ind_eq_true_iff
-- name    : BSLambda.Construction.ind_eq_true_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:13.583149+00:00
-- url     : https://prove2.me/theorems/5976cdd9-85d5-4055-9a56-4605571e2176
-- title:
--   Construction: ind eq true iff
-- statement:
--   A point is positive exactly when some certificate subcube contains it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L209-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L209-L210

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}
variable {x : Input (Coord ι r)}

theorem BSLambda.Construction.ind_eq_true_iff : ind Arc γ x = true ↔ ∃ i, (cert Arc γ i).Sat x := by sorry
