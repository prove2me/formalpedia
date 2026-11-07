-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_admissible_fullmask_predictable_exhaustion
-- name    : AvramDividend.Classical.avram_bv_meas7_original_admissible_fullmask_predictable_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:21:56.682611+00:00
-- url     : https://prove2.me/theorems/941b1def-1d17-44ec-b62b-0c2fbdc07b85
-- title:
--   Original admissible predictable stopped jump mask is the union of full compensated bands
-- statement:
--   For every original spectrally negative Lévy X and admissible dividend process D at any positive finite or infinite cap, construct a single deterministic cofinal full-band sequence valid at every finite stopped clock. The exact union equals the entire original strict positive pre-reserve interior and is predictable in the right-continuous original filtration. This connects the all-cap source masks used in finite-grid compensated-jump proofs to the unlocalised original predictable interior.
-- source:
--   Direct instantiation of the Proved all-cap compact full-band witnesses fc04d4a7, the child original stopped fullmask union proof, and the already Proved original interior predictability theorem 6fb43911. No new martingale, stochastic assumption or infinite-activity convergence is asserted.

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_allcap_full_predictable_compact_bands
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_stopped_fullmask_union_of_cofinal_bands
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_stopped_interior_zero_cap_predictable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_admissible_fullmask_predictable_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) ∧
      ∀ S : ℝ≥0,
        let τ : Ω → ℝ≥0 := fun ω =>
          (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
        let Z : ℝ≥0 × Ω → ℝ := fun p =>
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
        ((⋃ n : ℕ, {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Z p ∈ Icc (a n) (b n)}) =
          {p : ℝ≥0 × Ω |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            0 < Z p ∧ ENNReal.ofReal (Z p) < C}) ∧
        MeasurableSet[𝓕.rightCont.predictable]
          {p : ℝ≥0 × Ω |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            0 < Z p ∧ ENNReal.ofReal (Z p) < C} := by sorry
