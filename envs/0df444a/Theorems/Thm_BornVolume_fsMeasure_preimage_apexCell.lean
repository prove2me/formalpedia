-- Prove2me | Theorems.Thm_BornVolume_fsMeasure_preimage_apexCell
-- name    : BornVolume.fsMeasure_preimage_apexCell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:34.561804+00:00
-- url     : https://prove2.me/theorems/4d004d22-42ac-44b5-b7aa-2982829210b0
-- title:
--   Born Volume: fs Measure preimage apex Cell
-- statement:
--   **Born weights as Fubini–Study volumes, cell opposite the origin `0` (the last outcome).**
--   The same for the last coordinate, with weight `1 − ∑ b = ‖⟨e_M, ψ⟩‖²`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L209-L245
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L209-L245

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}

theorem BornVolume.fsMeasure_preimage_apexCell (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    fsMeasure p₀
        ((fun p => ratioN (fun j => momentMap p j))
          ⁻¹' ((fun x => apexLin (ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) x
              + ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) '' openSimplexFree))
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2) := by sorry
