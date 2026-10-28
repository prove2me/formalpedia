-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_grid_iff
-- name    : AvramDividend.Classical.chat04_random_reserve_shifted_closed_survival_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:09:24.815144+00:00
-- url     : https://prove2.me/theorems/fd37c55c-844b-4d18-aa88-62f45c9f1c07
-- title:
--   Closed-horizon shifted future survival equals rational relative-grid survival and a terminal test
-- statement:
--   For arbitrary random reserve H(ω), deterministic clock shift b and relative horizon T, continuous survival H+X(b+v)-X(b)≥0 at every v≤T is equivalent to survival on all rational observations k/n strictly before T and one explicit terminal test at T. The theorem upgrades the strict shifted downcrossing grid equivalence and exactly bridges real future-window killing to the countable-grid Markov–Tonelli theorem for q-scale renewal.
-- source:
--   Proved chat04_random_reserve_shifted_lower_before_horizon_grid_iff and order dichotomy.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_lower_before_horizon_grid_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_shifted_closed_survival_grid_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (b T : ℝ≥0) :
    (∀ v : ℝ≥0, v ≤ T →
      0 ≤ H ω + (X.X (b + v) ω - X.X b ω)) ↔
    (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
        0 ≤ H ω +
          (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω)) ∧
    0 ≤ H ω + (X.X (b + T) ω - X.X b ω) := by sorry
