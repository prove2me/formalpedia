-- Prove2me | Theorems.Thm_Auto_aux_twistedAverageAtScale_cuboidLift_eq
-- name    : Auto.aux_twistedAverageAtScale_cuboidLift_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:37.470942+00:00
-- url     : https://prove2.me/theorems/a2998397-a65d-4f3a-9c7f-f9b26fe71577
-- title:
--   Auto: aux twisted Average At Scale cuboid Lift eq
-- statement:
--   At a point of the base cuboid, the rescaled continuous average of the
--   cuboid lift is exactly the common-overlap width times the integer-lattice
--   discrete average.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1049-L1087
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1049-L1087

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_twistedAverageAtScale_cuboidLift_eq {n : ℕ}
    (hn : 0 < n) {ε δ : ℝ} (hε : ε < 1) (hεδ : ε ≤ δ)
    (hwidth : ε + δ < 1) (N : ℕ) (hN : 0 < N)
    (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (hu : ∀ i, 0 ≤ u i ∧ u i < ε) :
    ctTwistedAverageAtScale (N : ℝ) ctUnitIntervalKernel
        (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
        (WithLp.toLp 2 (fun j ↦ (k j : ℝ) + u j)) =
      aux_overlapWidth hn ε δ u * aux_integerDiscreteAverage N a k := by sorry
