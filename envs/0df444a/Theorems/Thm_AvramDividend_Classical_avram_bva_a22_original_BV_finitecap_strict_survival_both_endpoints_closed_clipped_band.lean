-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_finitecap_strict_survival_both_endpoints_closed_clipped_band
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_finitecap_strict_survival_both_endpoints_closed_clipped_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:45:44.64821+00:00
-- url     : https://prove2.me/theorems/3c01d6cd-23d8-4708-9069-4b1b204a5ef1
-- title:
--   Original finite-cap strict-survivor last and true horizon postpayment reserves share one deterministic closed zero-inclusive clipped band
-- statement:
--   For the genuine original Standing bounded-variation spectrally negative Lévy X with a finite cap, admissible dividend control D and the supplied physical strict uniform grid, on full-horizon strict-survival paths the post-rightpayment reserve at the last grid time and at the actual horizon both lie almost surely in the fixed closed interval [0, min(x+T drift,C.toReal)]. Original pre-ruin admissibility supplies nonnegativity, no-positive-jump BV supplies the drift upper envelope, and exact cap admissibility supplies the finite-cap upper envelope via the pinned ENNReal real-coercion equivalence. The interval includes zero and the finite-cap boundary, so C1 candidate monotonicity and a zero-boundary modulus can be applied to the actual source without a positive reserve floor. No surrogate process, global generator L1 or finite negative-jump activity is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_finitecap_strict_survival_both_endpoints_closed_clipped_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (hCfinite : C ≠ ⊤)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      (S : ℝ≥0∞) < ruinTime X x D ω →
      (x + X.X (u m (m + 1)) ω -
        rightLimit D (u m (m + 1)) ω) ∈
          Icc (0 : ℝ) (min (x + T * X.drift) C.toReal) ∧
      (x + X.X S ω - rightLimit D S ω) ∈
          Icc (0 : ℝ) (min (x + T * X.drift) C.toReal) := by sorry
