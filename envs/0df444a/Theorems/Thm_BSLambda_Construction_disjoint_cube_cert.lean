-- Prove2me | Theorems.Thm_BSLambda_Construction_disjoint_cube_cert
-- name    : BSLambda.Construction.disjoint_cube_cert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:57:06.826157+00:00
-- url     : https://prove2.me/theorems/5882d3f0-b6c5-4748-8cc1-2862e1e65614
-- title:
--   Construction: disjoint cube cert
-- statement:
--   Distinct certificate subcubes are disjoint (Section 4).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L102-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L102-L104

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}

theorem BSLambda.Construction.disjoint_cube_cert (hT : IsTournament Arc) (hij : i ≠ j) :
    Disjoint (cert Arc γ i).cube (cert Arc γ j).cube := by sorry
