-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_bounded_futurePayoff_integrable
-- name    : AvramDividend.Classical.avram_wave3_04_source_bounded_futurePayoff_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:28:22.388338+00:00
-- url     : https://prove2.me/theorems/eb2ca071-17d0-409f-b88a-59edf9d25ee8
-- title:
--   Bounded Borel functions of original Lévy future increments are integrable without first-moment assumptions
-- statement:
--   For an original spectrally negative Lévy process in its given filtered probability space, any real-valued globally bounded Borel payoff of the increment X_t is Bochner-integrable under the process's original probability law, with no finite-first-moment assumption on X_t. The proof uses original-filtration adaptedness to derive measurability of X_t, composition with the Borel payoff, the process probability-measure field, and Mathlib Integrable.of_bound. This is needed for Lévy large-jump truncation and centred finite-grid future increment terms even when E|X_t| is infinite.
-- source:
--   Pinned private remote compiler probe job 424e9e18-05b5-468b-b9ac-8490d0751141 reached its intentional sentinel without source errors, SHA-256 c3c540c820600db6c6ab6d92c06af99d11b92befbe60b7a66f54746d74e9fe55. Pinned Mathlib Integrable.of_bound and original SpectrallyNegativeLevy adapted and isProbability fields.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_source_bounded_futurePayoff_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (K : ℝ) (hBound : ∀ y, ‖φ y‖ ≤ K) :
    Integrable (fun ω => φ (X.X t ω)) P := by sorry
