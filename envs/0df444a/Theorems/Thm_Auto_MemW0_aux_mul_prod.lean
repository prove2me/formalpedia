-- Prove2me | Theorems.Thm_Auto_MemW0_aux_mul_prod
-- name    : Auto.MemW0.aux_mul_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:01.988864+00:00
-- url     : https://prove2.me/theorems/fc9e709c-908f-5c49-a56e-3914528a6f86
-- title:
--   Mem W0: aux mul prod
-- statement:
--   Binary tensor products preserve `W₀`.  This is the finite-product assertion from the draft,
--   written for the canonical product coordinates supplied by mathlib.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2157-L2169
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2157-L2169

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_mul_prod {E F 𝕜 : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)] [NormedAddCommGroup F]
    [ProperSpace F] [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)] [NormedField 𝕜]
    {f : E → 𝕜} {g : F → 𝕜} (hf : MemW0 f) (hg : MemW0 g) :
    MemW0 (fun x : E × F ↦ f x.1 * g x.2) := by sorry
