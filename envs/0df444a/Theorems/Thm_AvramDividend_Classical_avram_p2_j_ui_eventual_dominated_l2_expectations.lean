-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_dominated_l2_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_eventual_dominated_l2_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:21:59.170397+00:00
-- url     : https://prove2.me/theorems/ed971f69-dba8-4c55-bfcb-e28c31271803
-- title:
--   Eventual ENNReal-dominated second moments yield genuine real expectation convergence
-- statement:
--   For real random-variable mesh sums on the original probability space, use an arbitrary pointwise ENNReal envelope G_n dominating the signed real norm, with eventually uniformly bounded squared lintegrals, and an explicit almost-everywhere convergence hypothesis to infer integrability of the limit and convergence of genuine real Bochner expectations. This conditional theorem does not assume a càdlàg limit or a Lévy-rate identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_squared_enorm_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_l2_ae_expectations

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_eventual_dominated_l2_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (G : ℕ → Ω → ENNReal)
    (B : ℝ≥0) (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖Y n ω‖ₑ ≤ G n ω)
    (hB : ∀ n, N ≤ n →
      (∫⁻ ω, (G n ω) ^ (2 : ℝ) ∂P) ≤ (B : ENNReal) ^ 2)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
