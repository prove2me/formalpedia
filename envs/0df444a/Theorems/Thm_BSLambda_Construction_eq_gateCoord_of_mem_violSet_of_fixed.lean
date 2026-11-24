-- Prove2me | Theorems.Thm_BSLambda_Construction_eq_gateCoord_of_mem_violSet_of_fixed
-- name    : BSLambda.Construction.eq_gateCoord_of_mem_violSet_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:57:43.006065+00:00
-- url     : https://prove2.me/theorems/935c115d-3a0b-4d30-9740-fa5753064e90
-- title:
--   Construction: eq gate Coord of mem viol Set of fixed
-- statement:
--   Any violated literal of `C_j` at a point of `C_i` that is also fixed by `C_i` must be
--   the unique conflict `q_{ij}` (Section 4, used in Section 11.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L115-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L115-L124

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

theorem BSLambda.Construction.eq_gateCoord_of_mem_violSet_of_fixed (hT : IsTournament Arc)
    (hji : j ≠ i) (hij : Arc i j)
    {x : Input (Coord ι r)} (hx : (cert Arc γ i).Sat x) {v : Coord ι r}
    (hv : v ∈ (cert Arc γ j).violSet x) (hfix : v ∈ (cert Arc γ i).fixedSet) :
    v = gateCoord γ i j := by sorry
