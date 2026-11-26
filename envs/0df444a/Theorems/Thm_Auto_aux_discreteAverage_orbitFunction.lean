-- Prove2me | Theorems.Thm_Auto_aux_discreteAverage_orbitFunction
-- name    : Auto.aux_discreteAverage_orbitFunction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:13.307798+00:00
-- url     : https://prove2.me/theorems/a7ec2faa-76e3-5773-8c20-13bfdebf894c
-- title:
--   Auto: aux discrete Average orbit Function
-- statement:
--   The exact finite identity at the core of the ergodic-to-discrete
--   reduction.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1117-L1128
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1117-L1128

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

theorem Auto.aux_discreteAverage_orbitFunction {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n : ℕ}
    (S : ErgodicSystem X μ n) (f : Fin n → X → ℝ) (x : X)
    (k : Fin n → ℕ) (N : ℕ) :
    aux_discreteAverage N (aux_orbitFunction S f x) k =
      realErgodicAverage S N f (aux_orbit S.transformation k x) := by sorry
