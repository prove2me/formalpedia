-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_simple_weighted_centered_mean_zero
-- name    : AvramDividend.Classical.avram_a20_original_borel_simple_weighted_centered_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:49:39.81721+00:00
-- url     : https://prove2.me/theorems/ce00d3e6-3b93-4ce5-96cd-130eda52f60e
-- title:
--   Original physical finite Borel mark-simple weighted compensated sum is integrable with exact zero mean
-- statement:
--   For the actual original spectrally negative Lévy process under finite negative jump activity, any finite collection of measurable negative Borel marks and any real deterministic weights has an integrable weighted sum of its genuine physical marked counts compensated by the exact mean Tν(B). The expectation is zero. The proof applies the already Proved arbitrary negative-Borel real count first moment separately to each original marked cell, subtracts its deterministic rate and uses finite-sum linearity. This proves finite-weight source centring without assuming independent counts, Poisson laws or disjointness of mark sets; it supplies the missing centred L1 premise for exact raw weighted square-moment calculations using the Proved original finite-simple Borel L2 isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_simple_weighted_centered_mean_zero
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (F : Finset ι) (B : ι → Set ℝ) (a : ι → ℝ)
    (hB : ∀ i ∈ F, MeasurableSet (B i))
    (hNeg : ∀ i ∈ F, B i ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ι → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ι → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i
    let Z : Ω → ℝ := fun ω => ∑ i ∈ F, a i * Y i ω
    Integrable Z P ∧ (∫ ω, Z ω ∂P) = 0 := by sorry
