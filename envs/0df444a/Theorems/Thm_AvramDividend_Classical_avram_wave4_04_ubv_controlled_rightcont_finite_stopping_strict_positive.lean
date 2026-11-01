-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_controlled_rightcont_finite_stopping_strict_positive
-- name    : AvramDividend.Classical.avram_wave4_04_ubv_controlled_rightcont_finite_stopping_strict_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:34:30.297773+00:00
-- url     : https://prove2.me/theorems/9cc18bac-2e55-4eec-afe8-0888ccecff75
-- title:
--   Genuine UBV controlled reserve is positive at any right-continuous-filtration finite stopping time before ruin
-- statement:
--   For an original unbounded-variation spectrally negative Lévy process on filtration 𝓕 and the same actual dividend strategy D adapted to 𝓕, let τ be any finite stopping time for 𝓕.rightCont. Then almost surely, if τ is strictly earlier than the original ruinTime, the original reserve Uτ is strictly positive. This extends the Proved original-filtration finite-stopping version to right-continuous-filtration stopping clocks, as needed for a ruin-stopped stochastic verification argument. The proof uses the independently Proved identity-path/triplet 𝓕.rightCont Lévy transport Y; this is not a marginal-law coupling, because Y.X=X.X exactly on the same Ω. It transports D as a strategy and obtains pre-ruin nonnegativity from the unconditional original pathwise ruin-clock lemma. No extra pre-ruin nonnegativity binder or countable schedule is exposed. It does not provide a controlled Lévy-Itô/Itô-Meyer formula or the primary expected dividend bound.
-- source:
--   Original-X rightCont transport 006d14c7-93c5-47e0-bbf9-8c32b53d456b, control strategy transport bd2bcc87-3afa-47ef-bdbe-48e8f4379c0c, pathwise pre-ruin nonnegativity 03a69d71-1387-4410-83a2-1fe59054ebe6, and newly Proved same-filtration finite-stopping original controlled reserve  aa42a21a-9b17-47b3-b72d-a6efd383ae5c. Corrected primary 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_ubv_controlled_rightcont_finite_stopping_strict_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω →
      0 < riskProcess X x D (τ ω) ω := by sorry
