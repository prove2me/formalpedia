-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_raw_physical_J_eq_canonical_NX_integral
-- name    : AvramDividend.Classical.avram_bv_meas7_original_raw_physical_J_eq_canonical_NX_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:11:51.877571+00:00
-- url     : https://prove2.me/theorems/d340ac7d-093c-4258-8628-86b31e0a2e20
-- title:
--   The actual original signed physical jump witness equals the canonical intrinsic Levy jump integral almost everywhere
-- statement:
--   For the original bounded-variation spectrally negative Levy process X and original admissible D, any signed physical-grid marked-jump witness agrees almost everywhere with the intrinsic original-X jump integral. Its original-X.nu compensated difference is L1 and mean zero. This identifies the exact raw J in the cash-grid certificate with the canonical stochastic source M.
-- source:
--   This exact original-X physical-grid equality is proved by the already Proved 796b635d triangular-cell jump representation. The separately Proved d7a9acce arbitrary-raw-witness theorem supplies the matching L1 and zero-mean compensation. No extra integrability, drift or proxy-process hypothesis is added.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_signed_physical_raw_witness_L1_centered
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_centered_compensated_triangular_physical_H_cells

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_raw_physical_J_eq_canonical_NX_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ≥0) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n m : ℕ) (J : Ω → ℝ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict
        {z : ℝ≥0 | 0 < z ∧
          X.X z ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z,
          X.X z ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
    let Comp : Ω → ℝ := fun ω =>
      ∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)
    (∀ᵐ ω ∂P,
        let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        let Eω : Set (ℝ≥0 × ℝ) :=
          {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
        let A : ℝ≥0 × ℝ → ℝ := fun p =>
          if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
        let R : ℝ≥0 × ℝ → ℝ := fun p =>
          (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
            (if p ∈ Eω then A p else 0)
        let Δ : ℝ≥0 → ℝ := fun z =>
          X.X z ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) z
        let u : ℕ → ℝ≥0 := fun j =>
          min (((min j (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
        let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (R p)
        let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
          ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
            (if p ∈ Eω then A p else 0))
        J ω =
          (∑ j ∈ Finset.range (m + 1),
            ∑' z : ℝ≥0,
              if (0 < z ∧ Δ z ≠ 0) ∧ z ∈ Ioc (u j) (u (j + 1)) then
                Fp (z, Δ z) else 0).toReal -
          (∑ j ∈ Finset.range (m + 1),
            ∑' z : ℝ≥0,
              if (0 < z ∧ Δ z ≠ 0) ∧ z ∈ Ioc (u j) (u (j + 1)) then
                Fm (z, Δ z) else 0).toReal) →
      (∀ᵐ ω ∂P, J ω =
        ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) ∧
      Integrable (fun ω => J ω - Comp ω) P ∧
      (∫ ω, J ω - Comp ω ∂P) = 0 := by sorry
