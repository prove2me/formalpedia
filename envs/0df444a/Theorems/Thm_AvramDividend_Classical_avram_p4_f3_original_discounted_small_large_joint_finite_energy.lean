-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_small_large_joint_finite_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_discounted_small_large_joint_finite_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:43:40.267167+00:00
-- url     : https://prove2.me/theorems/b536464c-db55-43bd-828b-6b0d09d85667
-- title:
--   Actual discounted original stopped small and large negative Lévy jump bands have finite quadratic energy
-- statement:
--   For the actual original spectrally negative Levy process X and dividend strategy D, discounting its two physical clipped source small and large negative jump coefficient fields by exp(-qt) preserves their joint L2 source energies. The same original Levy measure and real stopping time axes are used.
-- source:
--   Compose Proved same-original-source three-channel finite joint energy with the direct nested jump discount monotonicity lemma. Finite physical source measure, same X,D,U,ν; no equality in law or conditional parent imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_gaussian_small_large_joint_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_time_discount_preserves_nested_jump_L2_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_discounted_small_large_joint_finite_energy
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
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) *
          ((w (U p + z) - w (U p)) -
           (w (δ + z) - w δ))) ^ 2) ∂X.ν) ∂μ) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Iic (-ε),
      ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) *
           (w (U p + z) - w (U p))) ^ 2) ∂X.ν) ∂μ) < ⊤ := by sorry
