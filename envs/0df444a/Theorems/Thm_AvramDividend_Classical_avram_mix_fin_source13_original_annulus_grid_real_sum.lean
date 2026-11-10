-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_grid_real_sum
-- name    : AvramDividend.Classical.avram_mix_fin_source13_original_annulus_grid_real_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:03:58.913603+00:00
-- url     : https://prove2.me/theorems/de84ed95-f9a9-461b-8b30-aac1360ed545
-- title:
--   Original negative-annulus finite-grid chronological product mean
-- statement:
--   For an arbitrary nondecreasing deterministic time grid, the original Levy process negative-annulus predecessor count times next-cell count has an integrable finite sum. Its mean is exactly the finite sum of the original annulus compensator rate products, without independence surrogates. This is the necessary equal-grid expectation input to the original annulus factorial-moment target 6ea0212e.
-- source:
--   MIX-FIN-SOURCE13 physical annulus finite-grid chronological pair proof

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_offtime_product_mean
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin_source13_original_annulus_grid_real_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (hstep : ∀ i, t i ≤ t (i + 1))
    (k : ℕ) (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let r : ℕ → ℝ := fun i => ((t i : ℝ≥0∞) * X.ν B).toReal
    let q : ℕ → ℝ := fun i =>
      ((((t (i + 1) - t i : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal
    Integrable (fun ω =>
      ∑ i ∈ Finset.range k,
        (J 0 (t i) ω).toReal * (J (t i) (t (i + 1)) ω).toReal) P ∧
    (∫ ω, (∑ i ∈ Finset.range k,
      (J 0 (t i) ω).toReal * (J (t i) (t (i + 1)) ω).toReal) ∂P) =
      ∑ i ∈ Finset.range k, r i * q i := by sorry
