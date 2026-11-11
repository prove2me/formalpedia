-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_smallband_physical_path_envelopes
-- name    : AvramDividend.Classical.avram_ja18_original_smallband_physical_path_envelopes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:12:41.070171+00:00
-- url     : https://prove2.me/theorems/23979329-54ba-459a-ba97-685ef26fe2a2
-- title:
--   Original full small-band jump path and uniform finite-horizon count envelope
-- statement:
--   Construct Jsmall as the physical original small negative-jump count-integral compensated on (-1,0) from X, preserving original Omega and filtration; finite overall negative intensity gives finitely many physical jumps on any horizon. Prove simultaneous finite-cutoff convergence, right-continuity, zero start, original-filtration conditional self-measurability, and an integrable uniform bound for Jsmall and all finite cutoffs on every finite horizon. Requires the original physical mark count expectation; never use large-jump first moments.
-- source:
--   Nontrivial analytic/pathwise child of 096ba1c2. Reuse Proved original physical jump-count and finite-simple compensator lemmas; separated from generic dominated martingale-limit transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_smallband_physical_path_envelopes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω) (Set.Ici t) t) ∧
      (∀ᵐ ω ∂P, Jsmall 0 ω = 0) ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont t) P (Jsmall t) ω = Jsmall t ω) ∧
      (∀ T : ℝ≥0, ∃ B : Ω → ℝ,
        Integrable B P ∧
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → ‖Jsmall t ω‖ ≤ B ω) ∧
        (∀ k : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
          ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤ B ω)) := by sorry
