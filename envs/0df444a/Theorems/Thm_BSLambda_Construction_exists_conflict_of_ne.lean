-- Prove2me | Theorems.Thm_BSLambda_Construction_exists_conflict_of_ne
-- name    : BSLambda.Construction.exists_conflict_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:46.589717+00:00
-- url     : https://prove2.me/theorems/f59e1df3-fa52-4c83-a25e-f44bdd3d4d3c
-- title:
--   Construction: exists conflict of ne
-- statement:
--   Distinct certificates always conflict: at the gate coordinate of whichever of the two
--   arcs joins `i` and `j` (Section 4).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L58-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L58-L61

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}

theorem BSLambda.Construction.exists_conflict_of_ne (hT : IsTournament Arc) (hij : i ≠ j) :
    ∃ v : Coord ι r, (cert Arc γ i).Conflict (cert Arc γ j) v := by sorry
