-- Prove2me | Theorems.Thm_BornVolume_born_weight_eq_measure_cell
-- name    : BornVolume.born_weight_eq_measure_cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:56.704221+00:00
-- url     : https://prove2.me/theorems/5a302de3-60e7-41ef-a70a-3b8aa046443e
-- title:
--   Born Volume: born weight eq measure cell
-- statement:
--   **Born weights are Fubini–Study volumes: the cell opposite vertex `i`.** Let `μ` be a unitarily
--   invariant probability measure on `ℂℙᴹ` and `ψ` a unit vector, with Born vector
--   `b = (‖ψ₀‖², …, ‖ψ_{M-1}‖²)` in free coordinates. The states whose Born vector lies in
--   `replaceMap b i '' openSimplexFree`, the cell opposite vertex `i` of the simplex coned from `b`,
--   have `μ`-measure equal to the Born weight `‖ψᵢ‖²`. The cell depends on `ψ`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L62-L73
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L62-L73

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

theorem BornVolume.born_weight_eq_measure_cell (μ : Measure (CPN (M + 1))) [IsProbabilityMeasure μ]
    (hμ : ∀ U : Matrix.unitaryGroup (Fin (M + 1)) ℂ, Measure.map (fun p => U • p) μ = μ)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1) (i : Fin M) :
    μ ((fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k)) ⁻¹'
        (replaceMap (fun k => ‖ψ (Fin.castSucc k)‖ ^ 2) i '' openSimplexFree))
      = ENNReal.ofReal (‖ψ (Fin.castSucc i)‖ ^ 2) := by sorry
