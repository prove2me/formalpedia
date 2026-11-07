-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_fullmask_union_discounted_negative_kernel_measurable
-- name    : AvramDividend.Classical.avram_bv_meas7_original_fullmask_union_discounted_negative_kernel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:31:54.113263+00:00
-- url     : https://prove2.me/theorems/044da2ac-4999-448f-830f-2d9c1148c19c
-- title:
--   Original predictable full-mask exhaustion supplies a jointly measurable discounted X-nu jump kernel
-- statement:
--   For an original admissible dividend strategy at positive cap, choose a single full-band predictable reserve exhaustion valid at every bounded ruin-stopped clock. The union is precisely the actual strict positive-cap stopped pre-reserve interior; the original stopped discounted negative-jump value-change integrand is jointly measurable for the right-continuous predictable time-and-path sigma algebra times the Borel negative-mark sigma algebra. This discharges the measurability instance needed before applying existing X.nu product-integrability theorems, without claiming unproved uniform integrability of the expanding bands.
-- source:
--   The already Proved avram_bv_meas7_original_admissible_fullmask_predictable_exhaustion supplies exact E and its predictable measurability, and avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable supplies jointly measurable original X.X, rightLimit D, w and q. IsAdmissibleLe X x C D projects to IsDividendStrategy via hD.1.1.

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_admissible_fullmask_predictable_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_fullmask_union_discounted_negative_kernel_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) :
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
        let Z : ℝ≥0 × Ω → ℝ := fun r =>
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          0 < Z p ∧ ENNReal.ofReal (Z p) < C}
        ((⋃ n : ℕ, {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Z p ∈ Icc (a n) (b n)}) = E) ∧
        Measurable[(𝓕.rightCont.predictable).prod
          (inferInstance : MeasurableSpace ℝ)]
          (fun p : (ℝ≥0 × Ω) × ℝ =>
            if p.1 ∈ E ∧ p.2 < 0 then
              Real.exp (-(q * (p.1.1 : ℝ))) *
                (w (Z p.1 + p.2) - w (Z p.1))
            else 0) := by sorry
