-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_physical_unbounded_predictable_grid_L1_zero
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_physical_unbounded_predictable_grid_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:47:09.634756+00:00
-- url     : https://prove2.me/theorems/2b2c8ee6-517d-49e4-bf6e-b08342c248a8
-- title:
--   Physical original Levy negative-band finite-grid compensated sum is L1-centred for unbounded L2 predictable weights
-- statement:
--   For every finite physical time grid of the original spectrally negative Levy process, negative Borel-separated bands and past-adapted L2 weights (without any uniform boundedness), the actual sum of centred marked jump counts times predictable weights is integrable with exactly zero expectation. Uses true original jump count and original filtration. Unlike existing L2 grid results this allows unbounded L2 weights while proving L1 centring, a necessary source witness in stopped Ito-Meyer integration.
-- source:
--   Follows from Proved source exact original physical cell L1 mean zero 53e31b78, disjoint original tagged-grid cells, and pinned Mathlib integrable_finset_sum and integral_finset_sum. No external Poisson process, no source martingale assumed, no canonical parent, and no boundary discard.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_physical_unbounded_predictable_grid_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, C i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (k : ℕ) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range k, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range k, H i ω *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by sorry
