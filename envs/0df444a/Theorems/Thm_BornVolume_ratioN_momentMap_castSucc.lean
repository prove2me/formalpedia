-- Prove2me | Theorems.Thm_BornVolume_ratioN_momentMap_castSucc
-- name    : BornVolume.ratioN_momentMap_castSucc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:24.192813+00:00
-- url     : https://prove2.me/theorems/4e96b142-dffb-42f8-a56b-a67309e66b01
-- title:
--   Born Volume: ratio N moment Map cast Succ
-- statement:
--   The `k`-th free moment coordinate of `[ψ]` is `‖⟨e_k, ψ⟩‖²`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellOpen.lean#L51-L57
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellOpen.lean#L51-L57

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

theorem BornVolume.ratioN_momentMap_castSucc (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (k : Fin M) :
    ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) k
      = ‖inner ℂ (EuclideanSpace.single (Fin.castSucc k) (1 : ℂ)) ψ‖ ^ 2 := by sorry
