-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_discreteAverage_truncated_orbit_eq
-- name    : Auto.aux_ErgodicBox.discreteAverage_truncated_orbit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:45:00.132811+00:00
-- url     : https://prove2.me/theorems/95d74564-daf3-5183-a9dd-efd1a10a46fe
-- title:
--   aux Ergodic Box: discrete Average truncated orbit eq
-- statement:
--   The aux Ergodic Box construction uses the discrete Average truncated orbit eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2933-L2956
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2933-L2956

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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.discreteAverage_truncated_orbit_eq {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n L M N : ℕ}
    (S : ErgodicSystem X μ n) (f : Fin n → X → ℝ) (x : X)
    (k : Fin n → ℕ) (hk : k ∈ box n L) (hN : N ≤ M) :
    aux_discreteAverage N
      (fun i ↦ truncOrbit
        (box n (L + M)) (aux_orbit S.transformation) (f i) x) k =
      aux_discreteAverage N (aux_orbitFunction S f x) k := by sorry
