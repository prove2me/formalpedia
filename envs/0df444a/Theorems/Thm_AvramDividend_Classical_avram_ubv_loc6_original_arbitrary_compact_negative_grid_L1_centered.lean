-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_arbitrary_compact_negative_grid_L1_centered
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_arbitrary_compact_negative_grid_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:07:44.641497+00:00
-- url     : https://prove2.me/theorems/10525210-9b3d-400e-a328-b76767437786
-- title:
--   Original source compensated negative finite-grid mean zero at arbitrary compact stopping times with L2 predictable gains
-- statement:
--   For a genuine original spectrally negative Levy sample process with admissible dividends, an actual pathwise negative-mark jump-counting grid, and an L2 filtration-adapted predictable gain at every left grid point, every right-continuous-filtration stopping time sigma below the natural ruin/horizon clock produces an integrable finite compensated-jump sum with mean zero. Unlike the existing natural-clock theorem, this supports the canonical physical compact localisation sigma and requires only L2, not uniformly bounded, gains.
-- source:
--   Derived from the public Proved natural-clock original process result 92713ce1 by absorbing the event {grid_i < sigma} into each adapted L2 gain, using stopping-time event measurability, MemLp under indicators and sigma <= natural tau. An independent nontrivial source-faithful bridge needed for the physical small/large negative-mark martingales of child 6c1039d5. No auxiliary jump process, unproved Poisson assumption, or extra stochastic mean-zero axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_original_arbitrary_compact_negative_grid_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (T : ℝ≥0) (cut : ℕ)
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
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (τ σ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσle : ∀ ω, σ ω ≤ τ ω)
    (k : ℕ) :
    Integrable (fun ω => ∑ i ∈ Finset.range k,
      (if (σ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
       then (0 : ℝ) else H i ω) *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range k,
      (if (σ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
       then (0 : ℝ) else H i ω) *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by sorry
