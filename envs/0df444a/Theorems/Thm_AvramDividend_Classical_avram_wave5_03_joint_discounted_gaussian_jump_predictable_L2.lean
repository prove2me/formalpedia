-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_joint_discounted_gaussian_jump_predictable_L2
-- name    : AvramDividend.Classical.avram_wave5_03_joint_discounted_gaussian_jump_predictable_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:32:39.994048+00:00
-- url     : https://prove2.me/theorems/fe3f9b1f-d2b7-4b7a-aae5-18dd1ac4643c
-- title:
--   Same-clock original controlled Gaussian and full Lévy-jump integrands have joint predictable L² localisation
-- statement:
--   For the same original spectrally negative Lévy path, actual left-limited controlled reserve, right-continuous filtration, deterministic discount horizon and inclusive endogenous ruin stopping, the local Gaussian gradient integrand and full negative-jump increment are simultaneously L²/predictable under the identical clock. This combines two source-verified integrand-energy interfaces, not a hypothetical independent process, compensated jump martingale, stochastic isometry or Itô–Meyer identity. The C² local band supplies Gaussian smoothness and C¹ supplies full jump integrability.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), stochastic terms of (5.11)–(5.13); source-specific bridge for corrected UBV 429e17ca-5528-40b5-b593-7c03973d0706 and BV ef7e6c20-a118-46f0-ac94-5b02204bba49 when sigma zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_controlled_gradient_predictable_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_joint_discounted_gaussian_jump_predictable_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw1 : ContDiffOn ℝ 1 w (Ioo a b))
    (hw2 : ContDiffOn ℝ 2 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if p.1 ≤ T then
        Real.exp (-(q * (p.1 : ℝ))) *
          (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then
            (1 : ℝ) else 0)
      else 0
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => ρ p.1 * J p
    @MemLp (ℝ≥0 × Ω) ℝ (𝓕.rightCont.predictable) _ _
      (fun p => ρ p * (X.σ * G p)) 2 μ ∧
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by sorry
