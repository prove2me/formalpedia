-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_finite_envelope_strong_L1
-- name    : AvramDividend.Classical.avram_p2_j_ui_eventual_finite_envelope_strong_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:47:07.095385+00:00
-- url     : https://prove2.me/theorems/9105a55a-bf16-4874-8853-d0ff4d8415a3
-- title:
--   Finite original-style ENNReal second-moment envelope implies strong L¹ convergence of dominated signed variables
-- statement:
--   On a probability space, real variables dominated almost everywhere by a nonnegative ENNReal envelope with eventually uniformly finite squared lintegral converge in L1 if they converge almost everywhere. Finite exceptional initial indices are allowed and the limit's L1 membership is proved. Handles exactly the finite ENNReal grid-moment constant supplied by original Lévy bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_squared_enorm_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_l2_strong_L1_convergence

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_eventual_finite_envelope_strong_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (G : ℕ → Ω → ENNReal)
    (K : ENNReal) (N : ℕ) (hK : K ≠ ⊤)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖Y n ω‖ₑ ≤ G n ω)
    (hB : ∀ n, N ≤ n → (∫⁻ ω, (G n ω) ^ (2 : ℝ) ∂P) ≤ K)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    MemLp Z 1 P ∧
      Tendsto (fun n => eLpNorm (Y n - Z) 1 P) atTop (nhds 0) := by sorry
