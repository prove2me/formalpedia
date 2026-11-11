-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18l_dominated_real_L1_norm_limit
-- name    : AvramDividend.Classical.avram_ja18l_dominated_real_L1_norm_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:11:57.652991+00:00
-- url     : https://prove2.me/theorems/becd9728-00fb-4a23-9a2e-6dd47a9b355b
-- title:
--   Dominated almost-everywhere convergence of real random variables gives L1 convergence on the original probability space
-- statement:
--   Given ambient-AE measurable real functions f_n, a common integrable real norm bound B, and almost-everywhere convergence f_n -> g, prove eLpNorm(f_n-g,1,P) -> 0. This is Lebesgue dominated convergence for the L1 distance and preserves the original measure.
-- source:
--   Analytic convergence half of generic sub-sigma-algebra closure K, needed for original adaptedness ed4dbe1a.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18l_dominated_real_L1_norm_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g B : Ω → ℝ)
    (hf : ∀ n : ℕ, AEStronglyMeasurable (f n) P)
    (hBi : Integrable B P)
    (hBound : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n : ℕ => eLpNorm (f n - g) 1 P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
