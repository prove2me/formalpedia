-- Prove2me | Theorems.Thm_BornVolume_map_ratioN_momentMap_fsMeasure
-- name    : BornVolume.map_ratioN_momentMap_fsMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:20.230922+00:00
-- url     : https://prove2.me/theorems/7d18c349-aafc-4116-b908-f438c04e4834
-- title:
--   Born Volume: map ratio N moment Map fs Measure
-- statement:
--   **The moment map pushes the Fubini–Study measure to the uniform measure on the
--   simplex.** The free-coordinate moment map `ratioN ∘ momentMap` pushes the Fubini–Study measure
--   on `ℂℙ^M` to `M!` times Lebesgue measure on the open simplex (the Dirichlet(1,…,1) law). For
--   `M = 1` this is Archimedes' hat-box theorem.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentDirichletN.lean#L60-L114
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentDirichletN.lean#L60-L114

module
public import Definitions.Def_BornVolumeLean_Volume_GaussianCPN
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
public import Definitions.Def_BornVolumeLean_Volume_MomentBridgeN
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}

theorem BornVolume.map_ratioN_momentMap_fsMeasure (p₀ : CPN (M + 1)) :
    Measure.map (fun p : CPN (M + 1) => ratioN (fun i => momentMap p i)) (fsMeasure p₀)
      = (Nat.factorial M : ℝ≥0∞) • volume.restrict openSimplexFree := by sorry
