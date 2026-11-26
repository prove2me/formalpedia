-- Prove2me | Theorems.Thm_Auto_aux_finite_forward_jump_bound_of_realVariable
-- name    : Auto.aux_finite_forward_jump_bound_of_realVariable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:43:44.951825+00:00
-- url     : https://prove2.me/theorems/28deab7d-a7a8-4030-ac7e-dadcffc7f119
-- title:
--   Auto: aux finite forward jump bound of real Variable
-- statement:
--   The continuous real-variable hypothesis bounds every finite portion of a
--   forward-lattice jump sum.  The data are first truncated only at sites read by
--   the finitely many output points under consideration.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2341-L2422
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2341-L2422

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

theorem Auto.aux_finite_forward_jump_bound_of_realVariable {n J : ℕ}
    (hn : 0 < n) (p : Fin n → ℝ≥0∞) (C : ℝ) (g : ℕ → ℝ)
    (hreal : realVariableJumpBound p C g) (hJ : 0 < J)
    (N : Fin (J + 1) → ℕ) (hN : StrictMono N)
    (hNpos : ∀ q, 0 < N q) (F : Fin n → (Fin n → ℕ) → ℝ)
    (A : Finset (Fin n → ℕ))
    (hp0 : ∀ i, p i ≠ 0) (hptop : ∀ i, p i ≠ ∞) :
    ∑ j : Fin J, ∑ k ∈ A,
      ‖aux_discreteAverage (N j.succ) F k -
        aux_discreteAverage (N j.castSucc) F k‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (((2 : ℝ) ^ (3 * n + 6)) * C) *
        ENNReal.ofReal (g J) *
          ∏ i, eLpNorm (F i) (p i) Measure.count ^ (2 : ℕ) := by sorry
