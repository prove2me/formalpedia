-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_Taylor_direct_finite_energy_and_compensator_bound
-- name    : AvramDividend.Classical.avram_wave6_02_actual_stopped_Taylor_direct_finite_energy_and_compensator_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:38:08.908227+00:00
-- url     : https://prove2.me/theorems/2a1bc6ba-9759-44c9-b9ee-b85cbe6395b7
-- title:
--   Self-contained original stopped Taylor finite marked physical L1 and L2 energy plus exact signed compensator error bound
-- statement:
--   Direct from actual original predictable physical stopped Taylor L1 and L2 energies, any positive tolerance admits finite marked predictable A with both physical excluded L1 and L2 norms small and signed source ν-compensator truncation bounded by its L1 norm; no intermediate jointly-constructed theorem import, no surrogate source, no raw first small-jump moment.
-- source:
--   Direct product Integrable GW and MemLp2 GW, finite sets via MemLp cutoff p1 and p2, union and eLpNorm_indicator_le, exact signed cutoff eLpNorm1 theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_product_Integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_Taylor_physical_signed_compensator_cutoff_error_le_eLpNorm_one_tail
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_stopped_Taylor_direct_finite_energy_and_compensator_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (ε : ℝ≥0∞) (hε : ε ≠ 0),
      ∃ A : Set (((ℝ≥0 × Ω) × ℝ)),
        MeasurableSet A ∧
        (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) A < ⊤ ∧
        eLpNorm (Aᶜ.indicator GW) (1 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) < ε ∧
        eLpNorm (Aᶜ.indicator GW) (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) < ε ∧
        |(∫ p, A.indicator GW p
            ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) -
          (∫ p, GW p
            ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))))| ≤
          (eLpNorm (Aᶜ.indicator GW) (1 : ℝ≥0∞)
            (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal) := by sorry
