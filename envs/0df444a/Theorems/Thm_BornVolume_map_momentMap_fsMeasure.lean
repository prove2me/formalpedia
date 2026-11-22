-- Prove2me | Theorems.Thm_BornVolume_map_momentMap_fsMeasure
-- name    : BornVolume.map_momentMap_fsMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:55.046915+00:00
-- url     : https://prove2.me/theorems/714be61c-e1a5-491a-a763-74ce7e1a5f06
-- title:
--   Born Volume: map moment Map fs Measure
-- statement:
--   The Fubini–Study form of `born_vector_uniform_of_invariant`: the free-coordinate moment map
--   pushes `fsMeasure p₀` forward to `M!` times Lebesgue measure on the open simplex.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L95-L100
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L95-L100

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

theorem BornVolume.map_momentMap_fsMeasure (p₀ : CPN (M + 1)) :
    Measure.map (fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k))
        (fsMeasure p₀)
      = (Nat.factorial M : ℝ≥0∞) • volume.restrict openSimplexFree := by sorry
