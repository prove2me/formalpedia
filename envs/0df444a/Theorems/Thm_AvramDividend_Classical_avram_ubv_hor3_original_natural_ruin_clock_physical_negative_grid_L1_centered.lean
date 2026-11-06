-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_natural_ruin_clock_physical_negative_grid_L1_centered
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_natural_ruin_clock_physical_negative_grid_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:54:16.045501+00:00
-- url     : https://prove2.me/theorems/92713ce1-4871-46dc-b559-9efea3c08878
-- title:
--   Actual clipped ruin-time stopped negative jump grid is source-integrable and mean zero without any clock or count-moment assumptions
-- statement:
--   For every original admissible dividend strategy D, the actual clipped natural ruinTime at deterministic Nat n admits a measurable right-continuous stopping clock τ such that every bounded-horizon finite grid of the intrinsic original Lévy marked negative-jump compensated increments, masked by the true stopped event τ≤grid(i), is integrable and exactly centred. The only stochastic coefficient conditions are original-filtration rightCont predictability and L2. This eliminates assumptions on stopped-clock existence, band intensity, and compensated-count L2 using already proved source results.
-- source:
--   Import Proved original ruin measurability bbfbecf4, rightCont stopping 2d036d4f, exact bounded-ruin clock witness d499e28b, and newly accepted physical finite-band stopped-grid integrability/zero  df69c43e. No proxy law or unproved martingale convergence. This is a finite-grid component for future original stopped Itô–Meyer.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_rightcont_stopped_finiteband_grid_L1_from_source
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_natural_ruin_clock_physical_negative_grid_L1_centered
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
    (k : ℕ) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      Measurable (fun ω => (τ ω : ℝ)) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range k,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
         then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
      (∫ ω, (∑ i ∈ Finset.range k,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
         then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) ∂P) = 0 := by sorry
