-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_integrable_from_finite_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_integrable_from_finite_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:17:49.383591+00:00
-- url     : https://prove2.me/theorems/74d7cc2e-ed75-4657-b645-148fe8f9ee9b
-- title:
--   Actual original controlled discounted Gaussian coefficient L1 from finite source L2 energy
-- statement:
--   For the same original controlled spectrally negative Levy X, dividend path D and clipped predividend reserve, finite quadratic energy of the discounted Gaussian coefficient on a finite physical source measure, together with its actual a.e. strong measurability, implies L1 Bochner integrability on that measure. This is the finite-source Ito stochastic integration coefficient integrability bridge; no substitution of the Levy process or zero-jump restriction.
-- source:
--   Apply the already proved same-source original discounted Gaussian square-energy result. Nonnegative squares and measurable source coefficient turn finite real-square lintegral into integrability of the square via Mathlib's lintegral_ofReal_ne_top_iff_integrable. Then the pinned memLp_two_iff_integrable_sq and MemLp.integrable with finite measure yield L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_physical_gaussian_finite_joint_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_integrable_from_finite_energy
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
    (hGm : AEStronglyMeasurable (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
           if y ∈ Icc δ K then y else δ))) μ) :
    Integrable (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
           if y ∈ Icc δ K then y else δ))) μ := by sorry
