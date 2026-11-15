-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB71_original_finitecap_caplinear_fullcell_positive_Taylor_cross_discount_bound
-- name    : AvramDividend.Classical.avram_gbB71_original_finitecap_caplinear_fullcell_positive_Taylor_cross_discount_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:19:33.154339+00:00
-- url     : https://prove2.me/theorems/5398bd43-425a-43e1-a018-15588a89b609
-- title:
--   Original finite-cap caplinear full Gaussian physical cells positive Taylor error dominated by three true source residual sums
-- statement:
--   For genuine original pure Gaussian Lévy source X, actual D right limit and full stopped physical cells with s_i+Δ≤ρ, the positive fullcell clipped discounted spatial generator remainder is bounded by the positive Taylor error, absolute Gaussian variance cross and positive discount error on exactly the original full-cell mask. This provides the one-sided pointwise estimate needed for source-faithful positive L1 B54.
-- source:
--   Instantiate Proved A137 original physical full-cell stopped Gaussian positive source error at the interior caplinear payoff V_b(z)=if z≤b then w(z) else w(b)+z-b, preserving the true source, dividend rightLimit, and stopping mask.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a137_original_physical_fullcell_positive_Taylor_cross_discount_pointwise_bound
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB71_original_finitecap_caplinear_fullcell_positive_Taylor_cross_discount_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (b : ℝ)
    (q : ℝ) (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Vb : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) *
      (deriv Vb (Y i) * Z i + (iteratedDeriv 2 Vb (Y i) / 2) *
        (Z i^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator Vb (Y i)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (Vb (Y i + R i) - Vb (Y i)) - H i
    let T : ℕ → ℝ := fun i => E (s i) *
      (Vb (Y i + R i) - Vb (Y i) - deriv Vb (Y i) * R i -
        (iteratedDeriv 2 Vb (Y i) / 2) * R i^2)
    let B : ℕ → ℝ := fun i => E (s i) *
      (iteratedDeriv 2 Vb (Y i) / 2) * (R i^2 - Z i^2)
    let C : ℕ → ℝ := fun i =>
      (E (s i + Δ) - E (s i)) * (Vb (Y i + R i) - Vb (Y i))
    let cut : ℕ → Prop := fun i => s i < ρ ∧ s i + Δ ≤ ρ
    max (∑ i ∈ Finset.range m, if cut i then F i else 0) 0 ≤
      max (∑ i ∈ Finset.range m, if cut i then T i else 0) 0 +
      |∑ i ∈ Finset.range m, if cut i then B i else 0| +
      max (∑ i ∈ Finset.range m, if cut i then C i else 0) 0 := by sorry
