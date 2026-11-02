-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_gaussian_localized_gradient_MemLp_two_export
-- name    : AvramDividend.Classical.avram_wave5_03a_original_gaussian_localized_gradient_MemLp_two_export
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:41:48.178535+00:00
-- url     : https://prove2.me/theorems/e6f5daf1-409e-4f21-a957-0611b7518032
-- title:
--   Public original-source predictable Gaussian-coefficient compact-band gradient L2 localisation
-- statement:
--   Public reusable interface proved on the actual SpectrallyNegativeLevy source and original predictable filtration: strict-prejump interior compact-band derivative times source Gaussian coefficient sigma and any predictable localisation weight of absolute value at most one is L2 against every finite predictable measure. This reproduces the canonically Proved private Wave5 Chat03-A localisation lemma using only public Proved Wave4 premises. It includes sigma=0, no Brownian copy, and does not assert stochastic integral existence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_controlled_gradient_predictable_MemLp_two

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_original_gaussian_localized_gradient_MemLp_two_export

    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (ρ : ℝ≥0 × Ω → ℝ)
    (hρ : Measurable[𝓕.rightCont.predictable] ρ)
    (hρbdd : ∀ p, |ρ p| ≤ 1)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    @MemLp (ℝ≥0 × Ω) ℝ (𝓕.rightCont.predictable)
      _ _ (fun p => ρ p * (X.σ * G p)) 2 μ := by
  sorry
