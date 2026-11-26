-- Prove2me | Theorems.Thm_Auto_MemW0_aux_comp_continuousLinearMap_of_measurePreserving
-- name    : Auto.MemW0.aux_comp_continuousLinearMap_of_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:00.485573+00:00
-- url     : https://prove2.me/theorems/3fdc3041-78ac-4371-90ef-fc53092ac0ee
-- title:
--   Mem W0: aux comp continuous Linear Map of measure Preserving
-- statement:
--   A measure-preserving linear change of variables transports Wiener-space membership once the
--   corresponding enlarged-radius envelope is integrable.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L319-L334
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L319-L334

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_comp_continuousLinearMap_of_measurePreserving
    {E F K : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [ProperSpace E] [ProperSpace F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F]
    [NormedAddCommGroup K] {f : F → K} (hf : MemW0 f) (e : E →L[ℝ] F)
    (he : MeasurePreserving e volume volume)
    (hr : Integrable (wienerEnvelope f ‖e‖)) :
    MemW0 (f ∘ e) := by sorry
