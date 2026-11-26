-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_le_sum_of_cover
-- name    : Auto.aux_wienerEnvelope_le_sum_of_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:50.656201+00:00
-- url     : https://prove2.me/theorems/78ceecea-d82b-5466-8db2-50be910dccec
-- title:
--   Auto: aux wiener Envelope le sum of cover
-- statement:
--   A finite cover of the large ball converts its local supremum into a finite sum of translates
--   of the small-radius local supremum.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L659-L678
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L659-L678

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_le_sum_of_cover {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (t : Finset E)
    (hcover : ∀ y ∈ closedBall (0 : E) s, ∃ z ∈ t, y ∈ closedBall z r) (x : E) :
    wienerEnvelope f s x ≤ ∑ z ∈ t, wienerEnvelope f r (x + z) := by sorry
