-- Prove2me | Theorems.Thm_BornVolume_blockSqNormCurry_map_pi
-- name    : BornVolume.blockSqNormCurry_map_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:08.788801+00:00
-- url     : https://prove2.me/theorems/773c7b26-6d2c-4f60-ba59-7cb472bd45d7
-- title:
--   Born Volume: block Sq Norm Curry map pi
-- statement:
--   The per-block squared-norm map `y ↦ (i ↦ y(i,0)² + y(i,1)²)`
--   pushes the standard Gaussian on `ℝ^{N×2}` (`gaussianReal^{⊗(N×2)}`) to the `N`-fold
--   product `Exp(1/2)^{⊗N}`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentBridgeN.lean#L52-L75
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentBridgeN.lean#L52-L75

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_PiCurry
public import Definitions.Def_BornVolumeLean_Volume_MomentBridgeN
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BornVolume

theorem BornVolume.blockSqNormCurry_map_pi {N : ℕ} :
    Measure.map (fun y : (Fin N × Fin 2) → ℝ => fun i => (y (i, 0)) ^ 2 + (y (i, 1)) ^ 2)
      (Measure.pi (fun _ : Fin N × Fin 2 => gaussianReal 0 1))
      = Measure.pi (fun _ : Fin N => expHalf) := by sorry
