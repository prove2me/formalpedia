-- Prove2me | Theorems.Thm_BornVolume_fs_volume_eq_dirichlet_inter
-- name    : BornVolume.fs_volume_eq_dirichlet_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:58.529572+00:00
-- url     : https://prove2.me/theorems/a7327b19-266f-4ed1-9710-805539ead9e4
-- title:
--   Born Volume: fs volume eq dirichlet inter
-- statement:
--   The volume law for an **arbitrary** measurable region `R` (no `R ⊆ openSimplexFree`):
--   the Fubini–Study measure of the preimage is `M!` times the Lebesgue measure of
--   `R ∩ openSimplexFree`. Used for the cells of measure zero.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L85-L90
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L85-L90

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

theorem BornVolume.fs_volume_eq_dirichlet_inter (p₀ : CPN (M + 1)) {R : Set (Fin M → ℝ)}
    (hR : MeasurableSet R) :
    fsMeasure p₀ ((fun p => ratioN (fun i => momentMap p i)) ⁻¹' R)
      = (Nat.factorial M : ℝ≥0∞) * volume (R ∩ openSimplexFree) := by sorry
