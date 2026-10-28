-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_survival_positive_deficit_measure_le_grid_cell_bound
-- name    : AvramDividend.Classical.bv_survival_positive_deficit_measure_le_grid_cell_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:53:23.393989+00:00
-- url     : https://prove2.me/theorems/bccfb5d8-47cc-43d1-ad1c-7ed91cd1a951
-- title:
--   Strict zero-barrier survival with positive deficit is bounded by a uniform grid-cell probability
-- statement:
--   For an actual bounded-variation spectrally negative Lévy process, strict survival with positive total drift deficit is almost surely covered by finitely many events where a single grid-cell deficit increment lies in (0,b]. If each such event has probability at most u, then survival with positive net deficit has probability at most N*u. No independence and no surrogate compound-Poisson law is used.
-- source:
--   Proved pathwise strict-survival mesh inclusion and generic finite measure union bound; Avram et al. (2007), section 3.3.

import Theorems.Thm_AvramDividend_Classical_bv_strict_survival_positive_deficit_grid_cell_ae
import Theorems.Thm_AvramDividend_Classical_finite_grid_event_measure_le_uniform_sum
import Mathlib.MeasureTheory.OuterMeasure.AE
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_survival_positive_deficit_measure_le_grid_cell_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0)
    (b : ℝ) (u : ℝ≥0∞)
    (hStep : ∀ k : ℕ, LT.lt k N → LE.le (ts k) (ts (k + 1)))
    (hWithin : ∀ k : ℕ, LT.lt k N → LE.le (ts (k + 1)) T)
    (hMesh : ∀ k : ℕ, LT.lt k N →
      LE.le (X.drift * ((ts (k + 1) : ℝ) - (ts k : ℝ))) b)
    (hCell : ∀ k : ℕ, LT.lt k N →
      LE.le (P {ω : Ω | 0 < (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) - (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧ (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) - (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b}) u) :
    LE.le
      (P {ω : Ω |
        (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
        X.drift * (ts 0 : ℝ) - X.X (ts 0) ω < X.drift * (ts N : ℝ) - X.X (ts N) ω})
      ((N : ℝ≥0∞) * u) := by sorry
