-- Prove2me | Theorems.Thm_BSLambda_Construction_one_le_dist_cert
-- name    : BSLambda.Construction.one_le_dist_cert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:12:18.196474+00:00
-- url     : https://prove2.me/theorems/c9921749-72c4-4e4f-b747-73c23376d5f3
-- title:
--   Construction: one le dist cert
-- statement:
--   A point of `C_i` is at distance at least `1` from `C_j` when `i ≠ j`; in particular
--   `C_i ∩ C_j = ∅` (Section 4).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L128-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L128-L130

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

theorem BSLambda.Construction.one_le_dist_cert (hT : IsTournament Arc) (hij : i ≠ j)
    {x : Input (Coord ι r)} (hx : (cert Arc γ i).Sat x) : 1 ≤ (cert Arc γ j).dist x := by sorry
