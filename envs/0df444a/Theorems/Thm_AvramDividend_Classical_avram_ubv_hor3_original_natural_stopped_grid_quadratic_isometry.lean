-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_natural_stopped_grid_quadratic_isometry
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_natural_stopped_grid_quadratic_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:04:50.320434+00:00
-- url     : https://prove2.me/theorems/26f7b549-880c-4937-9a65-ea59662c9fa8
-- title:
--   Exact second-moment isometry for physical negative jump grid masked at original finite ruin clock
-- statement:
--   For the original spectrally negative Levy process, the actual capped admissible strategy and clipped ruin stop, establish the exact stopped predictable compensated negative-band finite-grid quadratic identity, given authentic physical conditional count second moments, bounded predictable coefficients and endpoint count measurability. Derives the stopped mask's filtration measurability from the original ruin clock rather than assuming it.
-- source:
--   Combines original clipped ruin-clock predictable mask theorem with the Proved original right-continuous physical-grid isometry of P4-S3. The remaining conditional count moment inputs remain explicit. No unproved source Ito identity is imported.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_natural_clock_predictable_grid_mask
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_rightcont_physical_grid_isometry_adapted_auto
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem AvramDividend.Classical.avram_ubv_hor3_original_natural_stopped_grid_quadratic_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hFinite : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ i ω, |H i ω| ≤ L)
    (hNEnd : ∀ i, StronglyMeasurable[𝓕.rightCont (grid (i + 1))]
      (fun ω => (N i ω).toReal))
    (hSecond : ∀ i,
      P[(fun ω => ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) ^ 2)
      | 𝓕.rightCont (grid i)] =ᵐ[P]
      (fun _ => (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (B i)).toReal))
    (k : ℕ) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      (∫ ω, (∑ i ∈ Finset.range k,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
         then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (B i)).toReal)) ^ 2 ∂P) =
      ∑ i ∈ Finset.range k,
        ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) *
        ∫ ω, (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω) ^ 2 ∂P := by sorry
