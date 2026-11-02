-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_source_compensated_grid_martingale_step
-- name    : AvramDividend.Classical.avram_wave5_02b_original_source_compensated_grid_martingale_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:03:18.83567+00:00
-- url     : https://prove2.me/theorems/06c39fcc-1b60-4cd0-a44e-9762aa55d236
-- title:
--   Original source compensated marked grid has the discrete martingale step
-- statement:
--   On the original Lévy sample space and filtration, finite-grid sums of past-measurable coefficients times actual compensated marked-cell jump rewards satisfy the discrete martingale conditional-expectation step. Independence of each future reward from the original past is derived from a measurable shifted-source-path representation. The source-cell centring, square integrability, predictable-prefix integrability and measurability, and actual source representation remain explicit hypotheses; no auxiliary copy is used.
-- source:
--   Proved original shifted-future conditional moments af7a6ae1-9c80-4160-9501-5d24b1bfc27c and pinned Mathlib conditional expectation pull-out and addition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_future_path_conditional_first_second_moments

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave5_02b_original_source_compensated_grid_martingale_step
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
    (ν : Measure ℝ) (f : ℕ → ℝ → ℝ) (rate : ℕ → ℝ)
    (H Z : ℕ → Ω → ℝ)
    (hZsource : ∀ i ω, Z i ω =
      (∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
        f i p.2 ∂(NX ω)) - rate i * ∫ z, f i z ∂ν)
    (J : ℕ → (ℝ≥0 → ℝ) → ℝ) (hJ : ∀ i, Measurable (J i))
    (hRep : ∀ i ω, J i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) = Z i ω)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hZi : ∀ i, Integrable (Z i) P)
    (hZ2i : ∀ i, Integrable (fun ω => Z i ω ^ 2) P)
    (hProd : ∀ i, Integrable (H i * Z i) P)
    (hCenter : ∀ i, (∫ ω, Z i ω ∂P) = 0)
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, H j ω * Z j ω))
    (hPrefixI : ∀ i, Integrable
      (fun ω => ∑ j ∈ Finset.range i, H j ω * Z j ω) P)
    (hSigma : ∀ i, @SigmaFinite Ω (𝓕 (grid i))
      (P.trim (𝓕.le (grid i))))
    (n : ℕ) :
    P[(fun ω => ∑ i ∈ Finset.range (n + 1),
      H i ω * Z i ω) | 𝓕 (grid n)] =ᵐ[P]
        (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) := by sorry
