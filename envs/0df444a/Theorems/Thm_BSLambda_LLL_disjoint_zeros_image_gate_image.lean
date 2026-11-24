-- Prove2me | Theorems.Thm_BSLambda_LLL_disjoint_zeros_image_gate_image
-- name    : BSLambda.LLL.disjoint_zeros_image_gate_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:21.994882+00:00
-- url     : https://prove2.me/theorems/d0514ae9-796d-43f2-abfd-022f41c564e6
-- title:
--   LLL: disjoint zeros image gate image
-- statement:
--   The two halves of the violation set are disjoint: both halves shrink to the two halves
--   of `Construction.disjoint_block_image_gateCoord`, the owner block and the image of the full
--   out-neighbourhood.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L285-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L285-L292

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}

theorem BSLambda.LLL.disjoint_zeros_image_gate_image (Arc : ι → ι → Bool) (hT : IsTournament Arc)
    (γ : ι → ι → Fin r) (i : ι) (x : Input (Construction.Coord ι r)) :
    Disjoint ((zeroSet x i).image (fun k => ((i, k) : Construction.Coord ι r)))
      ((missSet Arc γ (zeroSet x) Finset.univ i).image (Construction.gateCoord γ i)) := by sorry
