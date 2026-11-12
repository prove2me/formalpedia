-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb46_stopped_H_uniform_absolute_bound
-- name    : AvramDividend.Classical.avram_gb46_stopped_H_uniform_absolute_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:55:10.518255+00:00
-- url     : https://prove2.me/theorems/f2f062d1-27ec-4458-adaa-f77d4080540e
-- title:
--   Uniform original finite-cap Hessian coefficient bound on stopped interior bands
-- statement:
--   For a finite dividend cap and a C2 value function on the interior, the stopped and discounted second-derivative coefficient on any positive interior compact band is bounded by one common constant. This is uniform in time, reserve, stopping rule, grid size and sample point; empty bands have coefficient zero. It isolates the deterministic bound required by original-process gb44.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb46_stopped_H_uniform_absolute_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ≥0) (ρ : Ω → ℝ≥0)
      (Y : Ω → ℝ) (ω : Ω),
      |if t < ρ ω then
        (1 / 2 : ℝ) * Real.exp (-(q * (t : ℝ))) *
          (if Y ω ∈ Icc (δ / 2)
            (C.toReal * (((j + 1 : ℕ) : ℝ) /
              ((j + 2 : ℕ) : ℝ))) then
              iteratedDeriv 2 w (Y ω) else 0)
      else 0| ≤ B := by
  sorry
