-- Prove2me | Theorems.Thm_BornVolume_one_sub_sum_ratioN_momentMap
-- name    : BornVolume.one_sub_sum_ratioN_momentMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:22.96483+00:00
-- url     : https://prove2.me/theorems/00883304-9c33-48d6-bf15-08efbd80e9c8
-- title:
--   Born Volume: one sub sum ratio N moment Map
-- statement:
--   One minus the sum of the free moment coordinates of `[ψ]` is `‖⟨e_M, ψ⟩‖²`, the last
--   coordinate.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellOpen.lean#L61-L72
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellOpen.lean#L61-L72

module
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}

theorem BornVolume.one_sub_sum_ratioN_momentMap (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) :
    (1 : ℝ) - ∑ k, ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) k
      = ‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2 := by sorry
