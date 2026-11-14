-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_compact_left_limit_uniform_discount_Riemann
-- name    : AvramDividend.Classical.avram_chat24_compact_left_limit_uniform_discount_Riemann
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T19:15:59.613407+00:00
-- url     : https://prove2.me/theorems/966a885e-1f3b-4988-ade7-7c1ab4049f80
-- title:
--   Uniform discount increment sums for compact paths with prescribed strict-left limits
-- statement:
--   A deterministic physical-time Riemann-sum theorem. A path F stays in a compact band up to B and has prescribed strict-left limit Y at every positive time up to B. For a continuous payoff on that band and nonnegative discount rate q, its exact uniform-grid discount-increment sums converge to the physical time integral of minus q times the discounted payoff of Y. The integrand is integrable. No convergence or measurability of F is assumed; these are obtained by step approximations. This is the deterministic analytic premise needed for actual-process parent b230d64f-4f55-4914-a750-0391902d27a6, whose known pre-ruin band theorem supplies hband and hpre.
-- source:
--   Source-faithful deterministic reduction of b230d64f-4f55-4914-a750-0391902d27a6, using the same B*(i/(n+1)) grids and original physical clock. Dominated convergence for measurable cell step approximants, using compact payoff boundedness and the derivative of exp(-qt).

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_compact_left_limit_uniform_discount_Riemann
    (F Y : ℝ≥0 → ℝ) (a b q T : ℝ) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (B : ℝ≥0) (hB : 0 < B) (hBT : B ≤ (⟨T, hT⟩ : ℝ≥0))
    (hband : ∀ s : ℝ≥0, s ≤ B → F s ∈ Icc a b)
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto F (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b)) :
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let A : ℝ≥0 → ℝ := fun t =>
      if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (-(q * w (Y t))) else 0
    Integrable A μ ∧
      Tendsto (fun n : ℕ =>
        let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
        ∑ i ∈ Finset.range (n + 1),
          (Real.exp (-(q * (u (i + 1) : ℝ))) -
            Real.exp (-(q * (u i : ℝ)))) * w (F (u i)))
        atTop (nhds (∫ t, A t ∂μ)) := by
  sorry
