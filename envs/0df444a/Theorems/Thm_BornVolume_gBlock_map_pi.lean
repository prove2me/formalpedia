-- Prove2me | Theorems.Thm_BornVolume_gBlock_map_pi
-- name    : BornVolume.gBlock_map_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:58.405811+00:00
-- url     : https://prove2.me/theorems/346253ef-3571-4805-8558-14760fce2daf
-- title:
--   Born Volume: g Block map pi
-- statement:
--   The single-block squared norm pushes the 2-fold standard Gaussian to
--   `Exp(1/2)`: `(fun w => w₀² + w₁²)∗ gaussianReal^{⊗2} = expHalf`. The `Fin 2 → ℝ`
--   form of `sqNorm_map_gaussian2` (`MomentMarginalUniform.lean`), routed through
--   `measurePreserving_piFinTwo` and `gaussian2_eq_prod`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentBridgeN.lean#L39-L47
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentBridgeN.lean#L39-L47

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

theorem BornVolume.gBlock_map_pi :
    Measure.map gBlock (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) = expHalf := by sorry
