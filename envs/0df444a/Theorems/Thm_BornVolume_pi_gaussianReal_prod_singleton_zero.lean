-- Prove2me | Theorems.Thm_BornVolume_pi_gaussianReal_prod_singleton_zero
-- name    : BornVolume.pi_gaussianReal_prod_singleton_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:17.040215+00:00
-- url     : https://prove2.me/theorems/ac07370b-fc7d-47af-babc-69896454acd1
-- title:
--   Born Volume: pi gaussian Real prod singleton zero
-- statement:
--   The standard Gaussian on `ℝ^{(M+1)×2}` has no atom at the origin.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentDirichletN.lean#L45-L54
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentDirichletN.lean#L45-L54

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

theorem BornVolume.pi_gaussianReal_prod_singleton_zero :
    Measure.pi (fun _ : Fin (M + 1) × Fin 2 => gaussianReal 0 1)
        {(0 : (Fin (M + 1) × Fin 2) → ℝ)} = 0 := by sorry
