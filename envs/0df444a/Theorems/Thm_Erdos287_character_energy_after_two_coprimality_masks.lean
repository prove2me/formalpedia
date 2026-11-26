-- Prove2me | Theorems.Thm_Erdos287_character_energy_after_two_coprimality_masks
-- name    : Erdos287.character_energy_after_two_coprimality_masks
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T21:40:01.337093+00:00
-- url     : https://prove2.me/theorems/a22216b7-dce9-44e6-8649-c1ff5912f809
-- title:
--   Character energy after two coprimality masks
-- statement:
--   Let A be arbitrary complex coefficients on the positive integers and let chi be completely multiplicative with absolute values at most one. For positive a and b, the squared absolute character sum on 1 through N restricted to integers coprime to ab is at most tau(a) tau(b) times the sum over d dividing a and v dividing b of the squared absolute character sums with coefficient A(dvj) on 1 through floor(N/(dv)).
-- source:
--   Erdős #287, mixed-residue Type II zero-frequency comparison.

import Mathlib

theorem Erdos287.character_energy_after_two_coprimality_masks (N a b : ℕ) (ha : 0 < a) (hb : 0 < b) (A χ : ℕ → ℂ)
    (hmul : ∀ d n, χ (d * n) = χ d * χ n) (hnorm : ∀ n, ‖χ n‖ ≤ 1) :
    ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime (a * b)), A n * χ n‖ ^ 2 ≤
      ((a.divisors.card : ℝ) * b.divisors.card) *
        ∑ d ∈ a.divisors, ∑ v ∈ b.divisors,
          ‖∑ j ∈ Finset.Icc 1 (N / (d * v)), A (d * v * j) * χ j‖ ^ 2 := by sorry
