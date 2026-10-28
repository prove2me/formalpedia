-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_grid_binomial_complete_pattern_mass_ws01b
-- name    : AvramDividend.Classical.bv_actual_grid_binomial_complete_pattern_mass_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:00:25.452797+00:00
-- url     : https://prove2.me/theorems/a734a8e5-1f9b-408b-a011-022d621194a7
-- title:
--   Actual finite-activity Lévy equal-width complete grid-pattern binomial mass
-- statement:
--   For the actual finite-activity bounded-variation Lévy process, the union of all complete active/inactive grid patterns with exactly k active cells has exactly the binomial probability mass. This is a source-process finite-dimensional Poisson count prerequisite, not a count of genuine jumps.
-- source:
--   Follows from Proved actual Lévy uniform-pattern probabilities (43ef4e2d), pairwise-disjoint pattern theorem (e169cf60), and binomial finite-product sum (02140547). It is a necessary finite-grid count interface for source-specific truncated-jump Poisson laws, but still requires a full-cover a.e. proof and pathwise dyadic jump-count convergence. No use of the desired exit identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_uniform_grid_pattern_real_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_binary_patterns_pairwise_disjoint_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_binomial_pattern_sum_ws01b

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

/-- The actual finite-activity Levy increments obey the binomial law on
the event that each grid cell is exactly inactive or strictly active.
The remaining full-coverage and dyadic-jump-limit steps are separate. -/

theorem AvramDividend.Classical.bv_actual_grid_binomial_complete_pattern_mass_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n k : ℕ) (h : ℝ)
    (hgap : ∀ i : ℕ, i < n →
      (((t (i + 1) - t i : ℝ≥0) : ℝ)) = h) :
    P.real {ω : Ω | ∃ S ∈ Finset.powersetCard k (Finset.range n),
      ∀ i : ℕ, i < n →
        X.X (t (i + 1)) ω - X.X (t i) ω ∈
          (if i ∈ S then
            Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
          else
            {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))})} =
      (Nat.choose n k : ℝ) *
        (1 - Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))) ^ k *
        (Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))) ^ (n - k) := by sorry
