-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_survivor_terminal_positive_omission_integrable_from_measurability
-- name    : AvramDividend.Classical.avram_bva_a22_original_survivor_terminal_positive_omission_integrable_from_measurability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:01:23.794451+00:00
-- url     : https://prove2.me/theorems/ed3daab5-71d2-452d-9261-0f9413c4964a
-- title:
--   Actual original positive true-horizon terminal omitted strip is row-integrable from its source measurability
-- statement:
--   For the original bounded-variation spectrally negative Levy source and dividend control, the genuine discounted full-horizon survivor terminal positive omission beyond the last physical uniform grid time is integrable in every row once its literal source expression is almost-everywhere strongly measurable. The already Proved original BV uniform deterministic terminal positive bound supplies a single K independent of row, and the original Lévy law is a probability measure. The nonnegative error has norm equal to itself, so the pinned Mathlib integrable-of-bound theorem yields integrability without global generator L1, finite jump activity, artificial spatial diagonal or other source substitution. The lemma targets the explicit omitted terminal term in BVA96.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_strict_survivor_true_terminal_positive_omission_uniform_L1_envelope
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_survivor_terminal_positive_omission_integrable_from_measurability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (x + X.X t ω - rightLimit D t ω))
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ m, AEStronglyMeasurable (Err m) P) →
    ∀ m, Integrable (Err m) P := by sorry
