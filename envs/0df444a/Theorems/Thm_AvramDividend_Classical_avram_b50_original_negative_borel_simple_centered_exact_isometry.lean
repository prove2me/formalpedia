-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b50_original_negative_borel_simple_centered_exact_isometry
-- name    : AvramDividend.Classical.avram_b50_original_negative_borel_simple_centered_exact_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:59:38.590199+00:00
-- url     : https://prove2.me/theorems/f0e8f691-6488-48f9-9a90-30e79dba2147
-- title:
--   Original negative marked Poisson simple compensated source has exactly zero mean and quadratic variance
-- statement:
--   For finite-activity original spectrally negative Levy jump counts on the original filtration, a finite real-weighted sum over disjoint negative Borel mark cells is integrable, exactly centred and square integrable with second moment equal to the sum of coefficient-squared times the true physical mark intensities. No independent noise representation and no global second mark moment are imposed.
-- source:
--   Proved original mark simple centred B49 and Proved original Borel marked stochastic isometry JA31.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b49_original_negative_borel_mark_simple_compensated_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_finite_borel_mark_source_isometry
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b50_original_negative_borel_simple_centered_exact_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i))
    (hNeg : ∀ i ∈ Finset.range K, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K,
      i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((t : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 t ×ˢ B i)).toReal - r i
    let G : Ω → ℝ := fun ω => ∑ i ∈ Finset.range K, c i * Y i ω
    Integrable G P ∧
    (∫ ω, G ω ∂P) = 0 ∧
    Integrable (fun ω => (G ω)^2) P ∧
    (∫ ω, (G ω)^2 ∂P) =
      ∑ i ∈ Finset.range K, (c i)^2 * r i := by sorry
