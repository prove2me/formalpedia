-- Prove2me | Theorems.Thm_BornVolume_freeMoment_eq_ratioN
-- name    : BornVolume.freeMoment_eq_ratioN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:36.200596+00:00
-- url     : https://prove2.me/theorems/e85ebb6b-9e01-46bf-a0c2-6d5bf9297547
-- title:
--   Born Volume: free Moment eq ratio N
-- statement:
--   In free coordinates, the moment map is `ratioN` of the full moment map, because the moment
--   coordinates sum to `1`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L44-L48
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L44-L48

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

theorem BornVolume.freeMoment_eq_ratioN :
    (fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k))
      = fun p : CPN (M + 1) => ratioN (fun i => momentMap p i) := by sorry
