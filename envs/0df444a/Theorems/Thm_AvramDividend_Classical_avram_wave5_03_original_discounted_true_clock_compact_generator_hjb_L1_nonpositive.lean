-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_discounted_true_clock_compact_generator_hjb_L1_nonpositive
-- name    : AvramDividend.Classical.avram_wave5_03_original_discounted_true_clock_compact_generator_hjb_L1_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:55:36.044085+00:00
-- url     : https://prove2.me/theorems/eaee29a0-44a3-42de-ad5c-257d0c0d8d0d
-- title:
--   Original source discounted stopped generator HJB residual is finite L1 and has nonpositive expectation on the exact predictable physical clock
-- statement:
--   The finite deterministic-horizon original P expected full discounted source generator-minus-q contribution, localized to compact positive prepayment reserves and stopped inclusively at the true ruinTime of the SAME controlled X,D, is signed Bochner L1 and nonpositive on a predictable clock that agrees with real Lebesgue time×P on every predictable set. Uses the Proved original source triplet pointwise identity, proved genuinely discounted predictable L1, and HJB generator≤0 only at interior states; exp(-qt) is strictly positive. This is the actual discounted generator drift inequality necessary for BV/UBV Itô–Meyer verification, not an assumed stochastic chain identity.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), full source discounted generator drift; accepted Chat03 original triplet identity 3ad3e17c and discounted true-clock L1 eaf85167; compatible with corrected UBV 429e17ca and BV ef7e6c20.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_compact_stopped_triplet_equals_full_generator
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_discounted_stopped_full_generator_triplet_true_clock_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_discounted_true_clock_compact_generator_hjb_L1_nonpositive
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
    (hw_gen : ∀ y : ℝ, 0 < y → y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (ρ p * (if Y p ∈ Icc (u + δ) v then
          X.generator w (Y p) - q * w (Y p) else 0))
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable R μ ∧
      (∫ p, R p ∂μ) ≤ 0 := by sorry
