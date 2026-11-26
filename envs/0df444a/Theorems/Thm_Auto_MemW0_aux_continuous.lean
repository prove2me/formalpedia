-- Prove2me | Theorems.Thm_Auto_MemW0_aux_continuous
-- name    : Auto.MemW0.aux_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:27.564275+00:00
-- url     : https://prove2.me/theorems/c574fa10-888f-5635-985c-a455caaba516
-- title:
--   Mem W0: aux continuous
-- statement:
--   Membership in `W₀` gives the defining continuity and integrability facts.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L233-L235
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L233-L235

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_continuous {E 𝕜 : Type*} [NormedAddCommGroup E] [MeasureSpace E]
    [NormedAddCommGroup 𝕜] {f : E → 𝕜} (hf : MemW0 f) : Continuous f := by sorry
