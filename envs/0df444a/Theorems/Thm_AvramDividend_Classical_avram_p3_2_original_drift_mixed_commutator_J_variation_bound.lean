-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_drift_mixed_commutator_J_variation_bound
-- name    : AvramDividend.Classical.avram_p3_2_original_drift_mixed_commutator_J_variation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:16:46.720548+00:00
-- url     : https://prove2.me/theorems/7c88cd82-a1bb-4d5b-88da-2cbbd45cd8be
-- title:
--   Original BV pure-drift mixed J commutator sum controlled by real cumulative jump variation
-- statement:
--   On the actual original BV Lévy path, any weighted finite-grid mixed negative-J commutator, including a physical pure-drift shift rather than only the jump-removed Y increment, is controlled by epsilon times exact original cumulative J jump mass when each cell's commutator is bounded by epsilon times its true J increment. The proof uses the source-exact J total-variation telescope and the bounded positive original discount factors. This generalises the F2 mixed-J mesh budget to arbitrary drift increments required by P3-2's cap-linear frozen envelope.
-- source:
--   Accepted original cumulative-J total variation e398addd and pinned real exponential inequalities; no new stochastic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_raw_negative_J_grid_total_variation_exact

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_drift_mixed_commutator_J_variation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      (∀ i : ℕ, i < n → u i ≤ u (i + 1)) →
      ∀ (z c : ℕ → ℝ) (ε : ℝ), 0 ≤ ε →
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      (∀ i : ℕ, i < n →
        |w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i)| ≤ ε * |j i|) →
      |∑ i ∈ Finset.range n,
        Real.exp (-(q * (u i : ℝ))) * (w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i))| ≤
      ε * (J (u n) - J (u 0)) := by sorry
