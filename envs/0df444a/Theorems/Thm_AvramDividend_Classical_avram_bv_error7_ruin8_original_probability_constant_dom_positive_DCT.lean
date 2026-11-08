-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_probability_constant_dom_positive_DCT
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_original_probability_constant_dom_positive_DCT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:54:54.927889+00:00
-- url     : https://prove2.me/theorems/c7fe2720-55d9-4a27-8b75-987e4e8c6d42
-- title:
--   Actual BV Lévy probability space absorbs positive contact errors with constant domination and almost-sure convergence
-- statement:
--   On the authentic Lévy probability space, uniformly bounded a.e.-measurable real contact errors converging to zero almost surely have positive parts converging to zero in expectation. This is the required noncircular DCT alternative for a derivative-free value-change contact at ruin.
-- source:
--   X.Standing supplies the original IsProbabilityMeasure P. The constant K is integrable; its domination establishes error integrability. The positive part is (Err+|Err|)/2, remains dominated by K, and tends to zero by continuity of max, so Bochner dominated convergence gives the expectation limit. This mirrors the already-Proved original source-mass DCT with a different, genuinely appropriate constant dominator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_original_probability_constant_dom_positive_DCT
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (K : ℝ) (hK : 0 ≤ K)
    (Err : ℕ → Ω → ℝ)
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P)
    (hErrAE : ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)))
    (hDom : ∀ m, ∀ᵐ ω ∂P, ‖Err m ω‖ ≤ K) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
