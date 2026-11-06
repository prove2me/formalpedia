-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_tagged_compact_lipschitz_commutator_bound
-- name    : AvramDividend.Classical.avram_p3_2_original_finite_tagged_compact_lipschitz_commutator_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:28:00.909475+00:00
-- url     : https://prove2.me/theorems/730499f4-06e9-498a-a497-7a0bf9b0bf8a
-- title:
--   Compact original reserve-band finite tagged nonlinear jump-cell commutator estimate
-- statement:
--   A finite physical jump-cell nonlinear commutator is bounded by weighted mark-size approximation and original prestate displacement errors when all four original reserve states in each cell lie in one compact interval and w is Lipschitz on that interval. This local condition is compatible with compact C1 localisation, without upgrading w to a globally Lipschitz function.
-- source:
--   Real triangle inequality and finite-weight nonnegative summation, as required by the original BV source finite-tag approximation and C1 compact reserve localisation.

import Mathlib

open scoped BigOperators
noncomputable section

/-- A compact-band Lipschitz estimate controls finite original physical jump
commutators whenever both pre- and post-jump reserve states remain in-band. -/

theorem AvramDividend.Classical.avram_p3_2_original_finite_tagged_compact_lipschitz_commutator_bound
    (w : ℝ → ℝ) (lo hi L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
      |w x - w y| ≤ L * |x - y|)
    (n : ℕ) (e z p j a : Fin n → ℝ)
    (he : ∀ i, 0 ≤ e i)
    (hPoints : ∀ i,
      z i ∈ Set.Icc lo hi ∧ z i - j i ∈ Set.Icc lo hi ∧
      p i ∈ Set.Icc lo hi ∧ p i - a i ∈ Set.Icc lo hi) :
    |∑ i : Fin n, e i *
      ((w (z i - j i) - w (z i)) -
        (w (p i - a i) - w (p i)))| ≤
      ∑ i : Fin n, e i *
        (L * |j i - a i| + 2 * L * |z i - p i|) := by sorry
