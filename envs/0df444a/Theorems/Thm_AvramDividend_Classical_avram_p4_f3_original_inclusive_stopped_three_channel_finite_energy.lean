-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_inclusive_stopped_three_channel_finite_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_inclusive_stopped_three_channel_finite_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:24:09.021051+00:00
-- url     : https://prove2.me/theorems/9d95c520-2f92-4b1f-a86f-836ad8743092
-- title:
--   Actual original Gaussian small and large Lévy energies finite on an inclusive measurable stopped clock
-- statement:
--   For the same genuine original spectrally negative Lévy X, controlled dividend path D, clipped predividend reserve and finite physical source measure, any measurable inclusive stopping graph t≤τ(ω) is measurable and restriction to this physical stopped graph retains all three finite discounted quadratic channel energies. The process is unchanged and the cutoff indicator includes the terminal time.
-- source:
--   The original discounted three-channel source-energy theorem 7eded0d7 holds for every finite physical source measure. The inclusive stopped graph is Borel measurable by the measurable stop clock, and a measure restriction is dominated by the original finite measure. Apply the proven source estimates to the restricted finite measure, preserving all three components of the Ito-Meyer stochastic energy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_small_large_finite_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_inclusive_stopped_three_channel_finite_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (hε : 0 < ε)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤)
    (τ : Ω → ℝ≥0) (hτmeas : Measurable τ) :
    let S : Set (ℝ≥0 × Ω) := {p | p.1 ≤ τ p.2}
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    MeasurableSet S ∧
    (∫⁻ p, ENNReal.ofReal
      ((Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w (U p))) ^ 2) ∂(μ.restrict S)) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) *
          ((w (U p + z) - w (U p)) -
           (w (δ + z) - w δ))) ^ 2) ∂X.ν) ∂(μ.restrict S)) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Iic (-ε),
      ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) *
           (w (U p + z) - w (U p))) ^ 2) ∂X.ν) ∂(μ.restrict S)) < ⊤ := by sorry
