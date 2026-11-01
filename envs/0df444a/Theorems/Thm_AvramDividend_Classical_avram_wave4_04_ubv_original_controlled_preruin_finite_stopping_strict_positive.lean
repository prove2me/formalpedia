-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
-- name    : AvramDividend.Classical.avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:17:26.321719+00:00
-- url     : https://prove2.me/theorems/aa42a21a-9b17-47b3-b72d-a6efd383ae5c
-- title:
--   Actual unbounded-variation controlled Lévy reserve stays strictly positive before ruin at finite stopping times
-- statement:
--   For the original spectrally negative Lévy process X with unbounded variation and an actual dividend strategy D adapted to the same filtration, let τ be any finite filtration stopping time. Assuming the source reserve is nonnegative strictly before its genuine first negative passage ruin time, then almost surely survival strictly beyond τ forces positive controlled reserve at τ. All stopping conditions, including past-event measurability, are explicit. From source downward regularity, a countable dense deterministic grid, cofinal horizons and the same-original-filtration finite-stopping strong-Markov theorem, obtain arbitrarily near negative X increments after τ. If the reserve were zero at τ, nondecreasing D would force genuine ruin within any surviving interval, contradiction. The dense/cofinal schedules are constructed within the proof and not exposed as external conditions. This is a same-X,D stochastic lower-boundary localisation tool; it is not an Itô-Meyer proof, not a finite-horizon discounted verification inequality, and does not assume a source jump compensator.
-- source:
--   Corrected UBV target 429e17ca-5528-40b5-b593-7c03973d0706 in mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Extends canonical fixed-time strictly positive reserve 78045b4c-083c-4a03-b6dd-ce6e0a01b53d to any finite stopping time. Uses source canonical downward regularity 703dc740-a8df-4cd1-9ff1-622fd81d68c7, dense-grid equivalence 561313a4-b044-4484-90c2-8cd1ceb9244e and same-filtration finite-stopping strong-Markov downcrossing 877dfbc1-79af-4667-be5c-d0fabce594c0. Private exact-125-line remote compiler job dfc34be0-11ec-450b-82f0-9780363fa134 reached sentinel with zero candidate errors, SHA-256 5407099e5c43775e2c02f3b61419de07533002c107eea65972517e0e40838003.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hPreNonneg : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ riskProcess X x D s ω)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω →
      0 < riskProcess X x D (τ ω) ω := by sorry
