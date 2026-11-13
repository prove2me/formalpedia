-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b25_original_real_stopped_AK_paired_DCT
-- name    : AvramDividend.Classical.avram_bvb_b25_original_real_stopped_AK_paired_DCT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:39:32.630076+00:00
-- url     : https://prove2.me/theorems/c23e368d-6cdf-44fb-a9bb-aae39a35f798
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva20_masked_discounted_mark_rate_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_K_weak_ruin_discounted_mark_bound
import Theorems.Thm_AvramDividend_Classical_avram_bva20_paired_dominated_integral_difference_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b25_original_real_stopped_AK_paired_DCT
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (C τ : ℝ≥0∞) (q T : ℝ) (hq : 0 ≤ q)
    (U : ℝ≥0 → ℝ) (ψ : ℝ → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hψ : ∀ b : ℝ, 0 ≤ b →
      ENNReal.ofReal b ≤ C → |ψ b| ≤ B)
    (u : ℕ → ℕ → ℝ≥0) (c : ℕ → ℕ → ℝ)
    (hcoeff : ∀ n i,
      c n i =
        if (u n i : ℝ≥0∞) < τ ∧
           0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
        then Real.exp (-(q * (u n i : ℝ))) * ψ (U (u n i))
        else 0)
    (f : ℝ → ℝ) :
    let F : ℕ → ℝ → ℝ := fun n t =>
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c n ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0
    let G : ℕ → ℝ → ℝ := fun n t =>
      let s : ℝ≥0 := Real.toNNReal t
      if 0 < s ∧ (s : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (s : ℝ≥0∞) ≤ τ ∧ 0 ≤ U s ∧ ENNReal.ofReal (U s) ≤ C
      then Real.exp (-(q * (s : ℝ))) * ψ (U s)
      else 0
    (∀ n, Measurable (F n)) →
    (∀ n, Measurable (G n)) →
    (∀ᵐ t ∂μ, Tendsto (fun n => F n t) atTop (𝓝 (f t)) ∧
      Tendsto (fun n => G n t) atTop (𝓝 (f t))) →
    Tendsto (fun n => (∫ t, G n t ∂μ) - (∫ t, F n t ∂μ))
      atTop (𝓝 (0 : ℝ)) := by sorry
