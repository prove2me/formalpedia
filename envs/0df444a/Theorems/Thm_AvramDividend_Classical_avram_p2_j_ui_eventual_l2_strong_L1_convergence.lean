-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_l2_strong_L1_convergence
-- name    : AvramDividend.Classical.avram_p2_j_ui_eventual_l2_strong_L1_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:35:51.634677+00:00
-- url     : https://prove2.me/theorems/1ee40d1e-0f35-478a-9c2e-7aea5a33111c
-- title:
--   A finite initial exceptional sequence of L² moments still yields strong L¹ convergence
-- statement:
--   For measurable real random variables converging almost everywhere under a probability law, if the L2 seminorms are bounded after a fixed finite index N then the almost-everywhere limit belongs to L1 and the original unshifted sequence converges in L1. The proof shifts indices, applies the genuine L2-to-L1 result, and transports back through atTop.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_strong_L1_convergence

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_eventual_l2_strong_L1_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, N ≤ n → eLpNorm (Y n) 2 P ≤ (B : ENNReal))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    MemLp Z 1 P ∧
      Tendsto (fun n => eLpNorm (Y n - Z) 1 P) atTop (nhds 0) := by sorry
