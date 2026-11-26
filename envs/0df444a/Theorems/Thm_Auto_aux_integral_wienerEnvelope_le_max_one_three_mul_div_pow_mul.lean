-- Prove2me | Theorems.Thm_Auto_aux_integral_wienerEnvelope_le_max_one_three_mul_div_pow_mul
-- name    : Auto.aux_integral_wienerEnvelope_le_max_one_three_mul_div_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:26.532734+00:00
-- url     : https://prove2.me/theorems/96848c8d-ed56-5db3-b82a-885014a29b51
-- title:
--   Auto: aux integral wiener Envelope le max one three mul div pow mul
-- statement:
--   The sharp radius comparison from the draft.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L854-L884
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L854-L884

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integral_wienerEnvelope_le_max_one_three_mul_div_pow_mul {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hfr : Integrable (wienerEnvelope f r)) :
    (∫ x, wienerEnvelope f s x) ≤
      max 1 ((3 * s / r) ^ d) * ∫ x, wienerEnvelope f r x := by sorry
