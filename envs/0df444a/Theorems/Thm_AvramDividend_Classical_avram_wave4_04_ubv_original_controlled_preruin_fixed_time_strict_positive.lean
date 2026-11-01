-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_controlled_preruin_fixed_time_strict_positive
-- name    : AvramDividend.Classical.avram_wave4_04_ubv_original_controlled_preruin_fixed_time_strict_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:27:49.95418+00:00
-- url     : https://prove2.me/theorems/78045b4c-083c-4a03-b6dd-ce6e0a01b53d
-- title:
--   Actual unbounded-variation controlled Lévy reserve is strictly positive before ruin at every fixed time
-- statement:
--   For the original unbounded-variation spectrally negative Lévy process X, an actual jointly adapted left-continuous increasing dividend path D, and a fixed deterministic time T, suppose the original reserve remains nonnegative strictly before ruin (as provided by source admissibility). Given a deterministic dense countable time schedule and a cofinal positive horizon sequence, with P-probability one any surviving reserve at T is strictly positive. The proof derives immediate downward regularity of the original source increments after T from canonical initial downward regularity, a dense-grid path law and same-filtration finite-stopping strong Markov theorem. If the controlled reserve were zero at T, its post-T values would become strictly negative arbitrarily soon because D cannot decrease. The actual strict ruin clock would then be ≤T, contradicting survival. No law-equal external X, source martingale claim or stochastic dividend verification bound is assumed. The dense-grid and horizon hypotheses are explicit constructive deterministic inputs to the published strong-Markov interface, not Lévy compensation premises.
-- source:
--   Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, corrected UBV core 429e17ca-5528-40b5-b593-7c03973d0706. Canonical Proved ae_negative_near_zero_of_unbounded_variation 703dc740-a8df-4cd1-9ff1-622fd81d68c7, levy_negative_before_horizon_iff_dense_grid 561313a4-b044-4484-90c2-8cd1ceb9244e, levy_finiteStopping_negative_near_zero_of_grid 877dfbc1-79af-4667-be5c-d0fabce594c0, pinned isStoppingTime_const and exact source ruinTime iInf definition. The hPreNonneg premise is already derived within the main corrected proof hPreRange from IsAdmissibleLe before ruin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_ubv_original_controlled_preruin_fixed_time_strict_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hPreNonneg : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ riskProcess X x D s ω)
    (T : ℝ≥0)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    ∀ᵐ ω ∂P, (T : ℝ≥0∞) < ruinTime X x D ω →
      0 < riskProcess X x D T ω := by sorry
