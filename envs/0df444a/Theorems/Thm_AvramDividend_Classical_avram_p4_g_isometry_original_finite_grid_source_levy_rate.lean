-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_source_levy_rate
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_source_levy_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:33:08.931454+00:00
-- url     : https://prove2.me/theorems/ecbdf566-1786-4528-9b07-0444241914f9
-- title:
--   Original Lévy intrinsic bounded-negative-band predictable grid L2 identity with exact ν intensity
-- statement:
--   A genuine original-source pathwise finite-grid square-integrability and L2 isometry: each count equals the intrinsic marked count of X, coefficients are measurable in the raw original past, and the right-hand-side intensity is the actual Lévy measure X.ν on negative marks strictly between -1 and -ε. Conditional assumptions include genuine original-source count extractors, finite-band Poisson laws, and past predictability. This theorem neither derives the original source Poisson law from first moments nor provides completion or stopped convergence.
-- source:
--   Direct exact-source ν-rate specialisation of proved c9733018-5e8f-4080-8323-c802bf9424c3 using a finite grid and source-mark rate equality.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_source_cell_counts_grid_l2_of_extractors

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_source_levy_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (grid : ℕ → ℝ≥0) (C : ℕ → Set ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hBand : ∀ i, C i ⊆ Set.Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (C i) < ⊤)
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (Fpath : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hFpath : ∀ i, Measurable (Fpath i))
    (hRep : ∀ i ω, Fpath i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) = K i ω)
    (hKsource : ∀ i ω, (K i ω : ℝ≥0∞) =
      NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hRate : ∀ i, (r i : ℝ) =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (C i)).toReal)
    (hH : ∀ i, Measurable[𝓕 (grid i)] (H i))
    (hHm : ∀ i, Measurable (H i))
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hKInt : ∀ i, Integrable
      (fun ω => (K i ω : ℝ) - (r i : ℝ)) P)
    (hPrefixPast : ∀ i, Measurable[𝓕 (grid i)] (fun ω =>
      ∑ j ∈ Finset.range i, H j ω * ((K j ω : ℝ) - (r j : ℝ))))
    (n : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range n, H i ω *
        ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
          (r i : ℝ))) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
        (r i : ℝ))) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n,
        ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal) * ∫ ω, (H i ω) ^ 2 ∂P := by sorry
