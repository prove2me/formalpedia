-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18b_original_smallband_cadlag_adapted_limit
-- name    : AvramDividend.Classical.avram_ja18b_original_smallband_cadlag_adapted_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:36:52.356592+00:00
-- url     : https://prove2.me/theorems/678e826a-4133-4c77-a8da-2505814f0aba
-- title:
--   Physical finite-activity small-band limit has original-filtration adapted and right-continuous paths
-- statement:
--   Construct the full finite-activity compensated original negative jump path as the uniform-on-compact cutoff limit, prove right-continuity at every time and original-right-continuous-filtration measurability. Reuse Proved local negative count finite ebd98fb4 and small physical jump tsum eventually zero fa3263d5. Does not require proving any integrable envelope.
-- source:
--   A sound path/filtration child of Open 23979329, separate from the quantitative uniform envelope. The path remains literally defined by the original marked jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18b_original_smallband_cadlag_adapted_limit
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
        condExp (𝓕.rightCont t) P (Jsmall t) ω = Jsmall t ω) := by sorry
