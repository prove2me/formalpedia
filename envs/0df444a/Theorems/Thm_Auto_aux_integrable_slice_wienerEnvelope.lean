-- Prove2me | Theorems.Thm_Auto_aux_integrable_slice_wienerEnvelope
-- name    : Auto.aux_integrable_slice_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:52:30.091022+00:00
-- url     : https://prove2.me/theorems/f2b8d67e-68ef-4770-a08d-029c2fe600a1
-- title:
--   Auto: aux integrable slice wiener Envelope
-- statement:
--   An integrable nonnegative continuous function on a Euclidean product has integrable
--   coordinate slices when its unit-ball Wiener envelope is integrable.  The proof uses Fubini on
--   the envelope and then moves to a nearby good slice; this avoids the unjustified
--   supremum-to-average step in the draft.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1353-L1374
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1353-L1374

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integrable_slice_wienerEnvelope {m l : ℕ}
    {G : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → ℝ}
    (hG : Continuous G) (hGnonneg : ∀ q, 0 ≤ G q)
    (hK : Integrable (wienerEnvelope G 1)) (u : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun v ↦ G (u, v)) := by sorry
