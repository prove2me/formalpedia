-- Prove2me | Theorems.Thm_Auto_aux_integerDiscreteAverage_natToInt
-- name    : Auto.aux_integerDiscreteAverage_natToInt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:56.068789+00:00
-- url     : https://prove2.me/theorems/26737d4c-0092-40cc-9f58-f17142140d99
-- title:
--   Auto: aux integer Discrete Average nat To Int
-- statement:
--   On the forward lattice, the integer-lattice average of the zero
--   extension is the original discrete average.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L313-L339
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L313-L339

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

theorem Auto.aux_integerDiscreteAverage_natToInt {n : ℕ} (N : ℕ)
    (F : Fin n → (Fin n → ℕ) → ℝ) (k : Fin n → ℕ) :
    aux_integerDiscreteAverage N (fun i ↦ aux_natToInt (F i))
      (fun j ↦ (k j : ℤ)) = aux_discreteAverage N F k := by sorry
