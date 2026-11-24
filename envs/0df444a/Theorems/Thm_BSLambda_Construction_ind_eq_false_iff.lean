-- Prove2me | Theorems.Thm_BSLambda_Construction_ind_eq_false_iff
-- name    : BSLambda.Construction.ind_eq_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:08.437843+00:00
-- url     : https://prove2.me/theorems/762f6b3a-4940-4ed8-b0b2-b327c75504a5
-- title:
--   Construction: ind eq false iff
-- statement:
--   A point is negative exactly when no certificate subcube contains it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L213-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L213-L214

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

theorem BSLambda.Construction.ind_eq_false_iff : ind Arc γ x = false ↔ ∀ i, ¬ (cert Arc γ i).Sat x := by sorry
