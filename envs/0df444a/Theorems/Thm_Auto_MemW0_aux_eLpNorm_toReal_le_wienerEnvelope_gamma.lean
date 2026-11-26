-- Prove2me | Theorems.Thm_Auto_MemW0_aux_eLpNorm_toReal_le_wienerEnvelope_gamma
-- name    : Auto.MemW0.aux_eLpNorm_toReal_le_wienerEnvelope_gamma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:56.906724+00:00
-- url     : https://prove2.me/theorems/01b08dd1-e123-55a1-98c8-ab8464a06700
-- title:
--   Mem W0: aux e Lp Norm to Real le wiener Envelope gamma
-- statement:
--   The preceding estimate with the unit-ball volume written in the gamma-function form used
--   in the draft.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1338-L1345
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1338-L1345

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_eLpNorm_toReal_le_wienerEnvelope_gamma {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f)
    {q : ℝ} (hq : 1 ≤ q) (hd : 0 < d) :
    (eLpNorm f (ENNReal.ofReal q) volume).toReal ≤
      ((Real.sqrt Real.pi) ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) ^ (q⁻¹ - 1) *
        ∫ x, wienerEnvelope f 1 x := by sorry
