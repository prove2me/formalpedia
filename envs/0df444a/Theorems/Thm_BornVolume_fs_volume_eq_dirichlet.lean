-- Prove2me | Theorems.Thm_BornVolume_fs_volume_eq_dirichlet
-- name    : BornVolume.fs_volume_eq_dirichlet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:57.171262+00:00
-- url     : https://prove2.me/theorems/defaf682-1b98-4915-8565-4a67c2a17ad0
-- title:
--   Born Volume: fs volume eq dirichlet
-- statement:
--   **The volume law on `ℂℙ^M`.** For a measurable region `R` of the free moment
--   simplex with `R ⊆ openSimplexFree`, the Fubini–Study measure of its preimage under the moment
--   map equals `M!` times the Lebesgue measure of `R`. A restatement of
--   `map_ratioN_momentMap_fsMeasure`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L47-L53
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L47-L53

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_VertexReplacement
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}

theorem BornVolume.fs_volume_eq_dirichlet (p₀ : CPN (M + 1)) {R : Set (Fin M → ℝ)}
    (hR : MeasurableSet R) (hRsub : R ⊆ openSimplexFree) :
    fsMeasure p₀ ((fun p => ratioN (fun i => momentMap p i)) ⁻¹' R)
      = (Nat.factorial M : ℝ≥0∞) * volume R := by sorry
