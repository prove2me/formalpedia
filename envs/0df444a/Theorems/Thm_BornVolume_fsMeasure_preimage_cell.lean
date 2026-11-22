-- Prove2me | Theorems.Thm_BornVolume_fsMeasure_preimage_cell
-- name    : BornVolume.fsMeasure_preimage_cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:29.723809+00:00
-- url     : https://prove2.me/theorems/3bd8242f-1d1e-4c67-a4b3-8edd7cc4eadc
-- title:
--   Born Volume: fs Measure preimage cell
-- statement:
--   **Born weights as Fubini–Study volumes, cell opposite vertex `i`.** For every unit `ψ`,
--   the states whose Born vector (in free coordinates) lies in the cell
--   `replaceMap b i '' openSimplexFree`, `b` the Born vector of `[ψ]`, have Fubini–Study measure
--   `‖⟨eᵢ, ψ⟩‖²`. Cells with `bᵢ > 0` by the subset lemma; cells with `bᵢ = 0` because the image has
--   determinant `0`, so it is Lebesgue-null, and `fs_volume_eq_dirichlet_inter` makes its preimage
--   null.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L171-L205
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L171-L205

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

theorem BornVolume.fsMeasure_preimage_cell (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin M) :
    fsMeasure p₀
        ((fun p => ratioN (fun j => momentMap p j))
          ⁻¹' (replaceMap (ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) i
            '' openSimplexFree))
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2) := by sorry
