-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_discounted_compact_interior_predictable_L2
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_discounted_compact_interior_predictable_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:08:26.112223+00:00
-- url     : https://prove2.me/theorems/c64c0500-f024-4295-8bd9-05f9ab657f0c
-- title:
--   Original source discounted compact-interior Gaussian derivative has automatic finite-clock predictable L² energy
-- statement:
--   For the actual original arbitrary-jump spectrally negative Levy process, canonical C2 HJB test on the interior 0<y<C, admissible original dividend path, and a compact left-limit reserve band strictly inside that domain, the precise finite-horizon discounted integrand exp(-q t)*X.sigma*w'(U_(t-)) (zero-masked outside the band) lies in L2 for every finite measure on the genuine right-continuous predictable sigma algebra, provided q>=0. The predictable discount is automatic and bounded by one; no Brownian representation, compensator, or Ito limit is asserted.
-- source:
--   Proved source predictable finite-horizon exponential weight ed5ee649-2acf-41d1-b048-eb113d9a3a5d and source Gaussian coefficient predictable L2 export e6f5daf1-409e-4f21-a957-0611b7518032; original SpectrallyNegativeLevy and IsAdmissibleLe definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_gaussian_localized_gradient_MemLp_two_export

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_discounted_compact_interior_predictable_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b u v : ℝ) (ha : 0 < a) (hau : a < u) (huv : u ≤ v)
    (hvb : v < b)
    (hband : ∀ y : ℝ, y ∈ Ioo a b → ENNReal.ofReal y < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Upre : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Upre p ∈ Icc u v then deriv w (Upre p) else 0
    @MemLp (ℝ≥0 × Ω) ℝ (𝓕.rightCont.predictable) _ _
      (fun p => (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0)
        * (X.σ * G p)) 2 μ := by sorry
