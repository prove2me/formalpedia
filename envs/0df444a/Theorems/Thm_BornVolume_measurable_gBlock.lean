-- Prove2me | Theorems.Thm_BornVolume_measurable_gBlock
-- name    : BornVolume.measurable_gBlock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:58.343827+00:00
-- url     : https://prove2.me/theorems/247cc9f0-4b6f-4720-ba18-931d90b64278
-- title:
--   Born Volume: measurable g Block
-- statement:
--   The Born Volume construction uses the measurable g Block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentBridgeN.lean#L33-L33
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentBridgeN.lean#L33-L33

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

theorem BornVolume.measurable_gBlock : Measurable gBlock := by sorry
