-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_finite_jump_energy_lower_of_cube_dom
-- name    : Auto.aux_CuboidNorm.finite_jump_energy_lower_of_cube_dom
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:42:33.306255+00:00
-- url     : https://prove2.me/theorems/5613b49e-1a8d-5afa-b31b-d8235f54fc23
-- title:
--   aux Cuboid Norm: finite jump energy lower of cube dom
-- statement:
--   Sum the finite base-cube lower bound over all adjacent scale pairs.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1929-L1958
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1929-L1958

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
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.finite_jump_energy_lower_of_cube_dom {n J : ℕ}
    {ε c : ℝ} (hε : ε ≤ 1) (hc : 0 ≤ c)
    (A : Finset (ZVector n)) (d : Fin J → ZVector n → ℝ)
    (G : Fin J → RVector n → ℝ)
    (hsupport : ∀ j k, k ∉ A → c * d j k = 0)
    (hdom : ∀ j k, k ∈ A → ∀ x, x ∈ latticeCuboid ε k →
      ‖c * d j k‖ₑ ≤ ‖G j x‖ₑ) :
    (ENNReal.ofReal c ^ (2 : ℝ) * ENNReal.ofReal ε ^ n) *
        ∑ j : Fin J, ∑ k ∈ A, ‖d j k‖ₑ ^ (2 : ℝ) ≤
      ∑ j : Fin J, eLpNorm (G j) (2 : ℝ≥0∞) volume ^ (2 : ℕ) := by sorry
