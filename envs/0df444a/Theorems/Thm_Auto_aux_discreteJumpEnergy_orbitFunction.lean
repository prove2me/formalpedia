-- Prove2me | Theorems.Thm_Auto_aux_discreteJumpEnergy_orbitFunction
-- name    : Auto.aux_discreteJumpEnergy_orbitFunction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:47:04.385333+00:00
-- url     : https://prove2.me/theorems/dc39a7d7-8534-483c-acb3-3ec19e2741ca
-- title:
--   Auto: aux discrete Jump Energy orbit Function
-- statement:
--   The discrete jump energy of orbit data is exactly the lattice sum of the
--   corresponding ergodic jump functions.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1134-L1151
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1134-L1151

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

theorem Auto.aux_discreteJumpEnergy_orbitFunction {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n J : ℕ}
    (S : ErgodicSystem X μ n) (N : Fin (J + 1) → ℕ)
    (f : Fin n → X → ℝ) (x : X) :
    aux_discreteJumpEnergy N (aux_orbitFunction S f x) =
      ∑ j : Fin J, eLpNorm
        (fun k ↦ realErgodicAverage S (N j.succ) f
            (aux_orbit S.transformation k x) -
          realErgodicAverage S (N j.castSucc) f
            (aux_orbit S.transformation k x)) 2 Measure.count ^ 2 := by sorry
