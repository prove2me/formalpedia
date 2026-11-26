-- Prove2me | Theorems.Thm_Auto_aux_integral_wienerEnvelope_le_card_mul_of_addHaar
-- name    : Auto.aux_integral_wienerEnvelope_le_card_mul_of_addHaar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:16.267689+00:00
-- url     : https://prove2.me/theorems/64fd1ab7-ffff-48ee-8bc1-d99f5808c26f
-- title:
--   Auto: aux integral wiener Envelope le card mul of add Haar
-- statement:
--   The finite-cover radius comparison is valid on every proper finite-dimensional Haar space.
--   This is the version used when an injective map is straightened to its range.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L704-L723
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L704-L723

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integral_wienerEnvelope_le_card_mul_of_addHaar {E F : Type*}
    [NormedAddCommGroup E] [ProperSpace E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddRightInvariant (volume : Measure E)] [NormedAddCommGroup F]
    {f : E → F} (hf : Continuous f) {r s : ℝ} (hr : 0 < r)
    (hs : 0 ≤ s) (hfr : Integrable (wienerEnvelope f r)) (t : Finset E)
    (hcover : ∀ y ∈ closedBall (0 : E) s, ∃ z ∈ t, y ∈ closedBall z r) :
    (∫ x, wienerEnvelope f s x) ≤ (t.card : ℝ) * ∫ x, wienerEnvelope f r x := by sorry
