-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_cash_canonical_source_every_physical_mesh
-- name    : AvramDividend.Classical.avram_bv_meas7_original_cash_canonical_source_every_physical_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:21:54.540472+00:00
-- url     : https://prove2.me/theorems/0ddc0e38-35a0-4859-aeaa-cd9698f8ecbb
-- title:
--   The original stopped BV cash inequality holds for every mesh with one canonical centred Lévy jump source
-- statement:
--   Fix the actual original bounded-variation Lévy process X, original admissible dividend D, cap, horizon and compact localisation band. The same intrinsic original-X compensated NX jump source and the same actual HJB generator source B satisfy the exact stopped physical cash/terminal inequality for every finite mesh m, retaining the raw contact/Taylor positive-error expression. Both source components are separately integrable, with mean-zero martingale and nonpositive mean generator, independent of m.
-- source:
--   Original Proved 3f1f67d4 gives the physical cash/source bound for every m with some raw J_m. Original raw-canonical bridge d340ac7d identifies J_m almost everywhere with the same intrinsic original NX jump integral, independently of m. Almost-everywhere congruence transfers the signed inequality, L1 and expectations. This isolates the remaining positive Taylor/contact error vanishing and terminal prefix interface.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_cash_grid_signed_witness_separately_centered
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_raw_physical_J_eq_canonical_NX_integral

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_cash_canonical_source_every_physical_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ≥0) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n : ℕ) :
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
    let F : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
         (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
            w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
         q * w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
      else 0
    let Comp : Ω → ℝ := fun ω =>
      ∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)
    let B : Ω → ℝ := fun ω =>
      ∫ t, F (t, ω)
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)
    let J : Ω → ℝ := fun ω =>
      ∫ p, H ((p.1, ω), p.2) ∂(NX ω)
    ∀ m : ℕ,
      (∀ᵐ ω ∂P,
        (let u : ℕ → ℝ≥0 := fun i =>
          min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
         let V : ℝ → ℝ := fun z =>
           if C = ⊤ then w z else if z ≤ C.toReal then w z
           else w C.toReal + (z - C.toReal)
         let cash : ℕ → ℝ := fun i =>
           (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
             ENNReal.ofReal (Real.exp (-(q * t)))
               ∂(dividendMeasure D ω)).toReal
         let post : ℕ → ℝ := fun i =>
           w (x + X.X (u i) ω - rightLimit D (u i) ω)
         let source : ℕ → ℝ := fun i =>
           V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           V (x + X.X (u i) ω - rightLimit D (u i) ω)
         0 < τ ω → ∃ k : ℕ, k ≤ m + 1 ∧ u k < τ ω ∧
           rightLimit D 0 ω +
             (∑ i ∈ Finset.range (m + 1), cash i) + post k ≤
           w x + (J ω - Comp ω + B ω) +
             max ((∑ i ∈ Finset.range k, source i) +
               (∑ i ∈ (Finset.range (m + 1)).filter
                 (fun i => u i < τ ω ∧ u (i + 1) = τ ω), cash i) -
               (J ω - Comp ω + B ω)) 0) ∧
        (let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
         let Eω : Set (ℝ≥0 × ℝ) :=
           {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
         let K : ℝ≥0 × ℝ → ℝ := fun p =>
           if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
         let R : ℝ≥0 × ℝ → ℝ := fun p =>
           (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
             (if p ∈ Eω then K p else 0)
         let Δ : ℝ≥0 → ℝ := fun v =>
           X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
         let u : ℕ → ℝ≥0 := fun i =>
           min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
         let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (R p)
         let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
           ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
             (if p ∈ Eω then K p else 0))
         J ω =
           (∑ i ∈ Finset.range (m + 1),
             ∑' v : ℝ≥0,
               if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
                 Fp (v, Δ v) else 0).toReal -
           (∑ i ∈ Finset.range (m + 1),
             ∑' v : ℝ≥0,
               if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
                 Fm (v, Δ v) else 0).toReal)) ∧
      Integrable (fun ω => J ω - Comp ω + B ω) P ∧
      (∫ ω, J ω - Comp ω + B ω ∂P) ≤ 0 ∧
      Integrable (fun ω => J ω - Comp ω) P ∧
      (∫ ω, J ω - Comp ω ∂P) = 0 ∧
      Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0 := by sorry
