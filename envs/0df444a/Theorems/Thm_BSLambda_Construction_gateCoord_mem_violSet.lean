-- Prove2me | Theorems.Thm_BSLambda_Construction_gateCoord_mem_violSet
-- name    : BSLambda.Construction.gateCoord_mem_violSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:57:08.723225+00:00
-- url     : https://prove2.me/theorems/ec3f4053-5a2d-4388-b971-ebe9ee5ff58d
-- title:
--   Construction: gate Coord mem viol Set
-- statement:
--   The unique conflict is always violated: `q_{ij} ∈ violSet (C_j) x` for `x ∈ C_i`
--   (Section 4).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L108-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L108-L111

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

theorem BSLambda.Construction.gateCoord_mem_violSet (hji : j ≠ i) (hij : Arc i j)
    {x : Input (Coord ι r)} (hx : (cert Arc γ i).Sat x) :
    gateCoord γ i j ∈ (cert Arc γ j).violSet x := by sorry
