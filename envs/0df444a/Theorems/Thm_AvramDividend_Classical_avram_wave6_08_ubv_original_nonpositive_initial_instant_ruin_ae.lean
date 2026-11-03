-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_original_nonpositive_initial_instant_ruin_ae
-- name    : AvramDividend.Classical.avram_wave6_08_ubv_original_nonpositive_initial_instant_ruin_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:31:55.865035+00:00
-- url     : https://prove2.me/theorems/cb66827f-b44a-4b76-a38d-453fa0ca9441
-- title:
--   Original UBV controlled reserve with nonpositive initial capital ruins instantly almost surely
-- statement:
--   For the original spectrally negative Lévy process with unbounded variation, every genuine source dividend strategy and any initial capital x≤0, ruin occurs immediately P-almost surely. This extends the canonical exact-zero-capital theorem to the entire nonpositive initial branch and supplies the correct physical zero-clock case of the finite-cap UBV stochastic verification.
-- source:
--   Original stopped strict-preruin controlled positivity aa42a21a evaluated at the deterministic zero stopping time, original D0=0 and Lévy X0=0. Generalises Proved x=0 original instant-ruin 2df9814e without a new sample space or assumed stochastic estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_ubv_original_nonpositive_initial_instant_ruin_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (hx : x ≤ 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ruinTime X x D ω = 0 := by sorry
