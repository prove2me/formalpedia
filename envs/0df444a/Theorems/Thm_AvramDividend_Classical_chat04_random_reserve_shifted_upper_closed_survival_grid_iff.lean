-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_upper_closed_survival_grid_iff
-- name    : AvramDividend.Classical.chat04_random_reserve_shifted_upper_closed_survival_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:48:55.97339+00:00
-- url     : https://prove2.me/theorems/3781c557-ac45-4b5f-94fd-4a5fa0d84ce8
-- title:
--   Finite-horizon shifted upper-barrier survival equals rational-grid tests and a terminal test
-- statement:
--   For any path-dependent initial reserve H, clock shift b, upper barrier a and horizon T, the shifted Lévy reserve remains at or below the barrier at every time up to T if and only if it does so at every rational grid point strictly before T and at T. The terminal test handles endpoint crossings without continuity assumptions. This is a direct upper-barrier analogue of the Proved nonnegative lower-survival equivalence.
-- source:
--   Proved shifted upper-before-horizon rational-grid crossing equivalence and classical linear order duality.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_upper_before_horizon_grid_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_shifted_upper_closed_survival_grid_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0) :
    (∀ v : ℝ≥0, v ≤ T →
      H ω + (X.X (b + v) ω - X.X b ω) ≤ a) ↔
    (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
        H ω +
          (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω) ≤ a) ∧
    H ω + (X.X (b + T) ω - X.X b ω) ≤ a := by sorry
