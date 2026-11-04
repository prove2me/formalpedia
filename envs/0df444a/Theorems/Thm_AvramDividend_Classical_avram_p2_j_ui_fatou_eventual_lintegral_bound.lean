-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_fatou_eventual_lintegral_bound
-- name    : AvramDividend.Classical.avram_p2_j_ui_fatou_eventual_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:32:11.044856+00:00
-- url     : https://prove2.me/theorems/027e9791-2484-434e-96b5-c3ce4c145ee6
-- title:
--   Fatou passes eventual ENNReal lintegral envelopes to an almost-everywhere limit
-- statement:
--   For any measure and a sequence of measurable ENNReal functions converging almost everywhere to V, an eventual common ENNReal upper bound K on their lintegrals bounds the lintegral of V. This quantifies the finite-initial-exception principle for second-moment envelopes and allows source sums to inherit integrability after a genuine mesh limit is established.

import Mathlib

open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_fatou_eventual_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ENNReal) (V : Ω → ENNReal)
    (K : ENNReal) (hm : ∀ n, Measurable (F n))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds (V ω)))
    (hB : ∀ᶠ n : ℕ in atTop, (∫⁻ ω, F n ω ∂P) ≤ K) :
    (∫⁻ ω, V ω ∂P) ≤ K := by sorry
