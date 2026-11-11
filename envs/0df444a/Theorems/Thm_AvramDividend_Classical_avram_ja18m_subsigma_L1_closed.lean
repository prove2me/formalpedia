-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18m_subsigma_L1_closed
-- name    : AvramDividend.Classical.avram_ja18m_subsigma_L1_closed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:11:52.712876+00:00
-- url     : https://prove2.me/theorems/9b571a6f-90d3-4b63-9742-218be7354ee4
-- title:
--   A sub-sigma-algebra measurable L1 sequence has a sub-sigma-algebra measurable L1 limit
-- statement:
--   For m <= m0, if f_n are each m-AE strongly measurable and L1, g is ambient L1, and eLpNorm(f_n-g,1,P) tends to zero, conclude g is m-AE strongly measurable under the same original measure. This should follow by Mathlib isClosed_aestronglyMeasurable on Lp space and L1 distance convergence.
-- source:
--   Closed-subspace half of generic sub-sigma-algebra closure K, needed for original adaptedness ed4dbe1a.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18m_subsigma_L1_closed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) (hSub : m ≤ mΩ)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n : ℕ, AEStronglyMeasurable[m] (f n) P)
    (hfi : ∀ n : ℕ, MemLp (f n) 1 P)
    (hgi : MemLp g 1 P)
    (hNorm : Tendsto (fun n : ℕ => eLpNorm (f n - g) 1 P)
      atTop (𝓝 (0 : ℝ≥0∞))) :
    AEStronglyMeasurable[m] g P := by sorry
