-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_single_positive_clock_reset_admissible
-- name    : AvramDividend.Classical.avram_bv_tail12_single_positive_clock_reset_admissible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:23:00.972898+00:00
-- url     : https://prove2.me/theorems/43840985-08f7-44ad-ae97-e9eaa2b9e502
-- title:
--   A single affordable positive-time right dividend reset is admissible at infinite cap
-- statement:
--   For an original spectrally negative Levy process and a deterministic positive reset time, a left-continuous dividend strategy that is zero up to the reset and pays an amount thereafter is infinitely capped admissible whenever the stated strategy and right-limit identities hold and the payment at the reset is affordable strictly before ruin. This moves initial-only lump-sum admissibility to a positive deterministic clock.
-- source:
--   Adapts accepted source-exact initial step theorem be720d99 and public Proved riskProcess_nonneg_before_ruin c26c83f7. Needed for the one-reset validity audit of canonical 0b2da5b3, with the later full IsDividendStrategy and rightLimit proofs still separate.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail12_single_positive_clock_reset_admissible
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (s : ℝ≥0) (hs : 0 < s) (K : Ω → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω)
    (hstrategy : IsDividendStrategy 𝓕 D)
    (hright : ∀ ω t, rightLimit D t ω = if t < s then 0 else K ω)
    (hafford : ∀ ω, (s : ℝ≥0∞) < ruinTime X x D ω →
      K ω ≤ x + X.X s ω) :
    IsAdmissibleLe X x ⊤ D := by sorry
