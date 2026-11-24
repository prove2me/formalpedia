-- Prove2me | Theorems.Thm_BSLambda_Construction_eq_gateCoord_of_conflict
-- name    : BSLambda.Construction.eq_gateCoord_of_conflict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:19.825162+00:00
-- url     : https://prove2.me/theorems/e95cf68c-6472-4093-984d-cfe9d1969113
-- title:
--   Construction: eq gate Coord of conflict
-- statement:
--   `q_{ij}` is the *unique* conflicting literal between `C_i` and `C_j` (Section 4).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L64-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L64-L74

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

theorem BSLambda.Construction.eq_gateCoord_of_conflict (hT : IsTournament Arc)
    (hji : j ≠ i) (hij : Arc i j) {v : Coord ι r}
    (h : (cert Arc γ i).Conflict (cert Arc γ j) v) : v = gateCoord γ i j := by sorry
