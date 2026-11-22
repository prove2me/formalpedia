-- Prove2me | Theorems.Thm_BornVolume_born_weight_eq_measure_apexCell
-- name    : BornVolume.born_weight_eq_measure_apexCell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:45.888784+00:00
-- url     : https://prove2.me/theorems/4e92ee75-7963-48dd-8e59-484f5dd6e8b2
-- title:
--   Born Volume: born weight eq measure apex Cell
-- statement:
--   **Born weights are Fubini–Study volumes: the cell opposite the last vertex.** With `μ`, `ψ`
--   and `b` as in `born_weight_eq_measure_cell`, the states whose Born vector lies in the cell opposite
--   the last vertex, the image of the open simplex under the affine map `x ↦ apexLin b x + b`, have
--   `μ`-measure equal to the Born weight `‖ψ_M‖²`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L79-L91
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L79-L91

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}

theorem BornVolume.born_weight_eq_measure_apexCell (μ : Measure (CPN (M + 1))) [IsProbabilityMeasure μ]
    (hμ : ∀ U : Matrix.unitaryGroup (Fin (M + 1)) ℂ, Measure.map (fun p => U • p) μ = μ)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1) :
    μ ((fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k)) ⁻¹'
        ((fun x => apexLin (fun k => ‖ψ (Fin.castSucc k)‖ ^ 2) x
          + fun k => ‖ψ (Fin.castSucc k)‖ ^ 2) '' openSimplexFree))
      = ENNReal.ofReal (‖ψ (Fin.last M)‖ ^ 2) := by sorry
