-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a265_small_budget_large_L1_positive_source_gluing
-- name    : AvramDividend.Classical.avram_ga_a265_small_budget_large_L1_positive_source_gluing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:54:55.96635+00:00
-- url     : https://prove2.me/theorems/d902d8ab-2940-433f-b564-bad9a266b97f
-- title:
--   Gaussian combined source positive L1 from arbitrarily small small-cell budgets and vanishing large-cell expected errors
-- statement:
--   For nonnegative integrable positive-part source F and a δ-dependent small/large partition bound, if every fixed δ yields a large-cell expected positive error converging to zero and the small-cell expected error can be made eventually arbitrarily small by choosing δ from any requested tolerance, then the full expected positive residual converges to zero. This is the exact quantifier-sensitive gluing for the original a216 Gaussian finite physical-cell source: a263 supplies large Gaussian tail L1 and a264 supplies Taylor-modulus small Gaussian source budget.
-- source:
--   Original a216 analytic finite-grid small/large partition quantified gluing; proof by Metric.tendsto_atTop and integral_mono

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a265_small_budget_large_L1_positive_source_gluing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (S L : ℝ → ℕ → Ω → ℝ)
    (hFI : ∀ m, Integrable (fun ω => max (F m ω) 0) P)
    (hSI : ∀ δ, 0 < δ → ∀ m,
      Integrable (fun ω => max (S δ m ω) 0) P)
    (hLI : ∀ δ, 0 < δ → ∀ m,
      Integrable (fun ω => max (L δ m ω) 0) P)
    (hPt : ∀ δ, 0 < δ → ∀ m ω,
      max (F m ω) 0 ≤
        max (S δ m ω) 0 + max (L δ m ω) 0)
    (hL : ∀ δ, 0 < δ →
      Tendsto (fun m => ∫ ω, max (L δ m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)))
    (hS : ∀ η, 0 < η →
      ∃ δ, 0 < δ ∧ ∃ k : ℕ, ∀ m, k ≤ m →
        (∫ ω, max (S δ m ω) 0 ∂P) ≤ η) :
    Tendsto (fun m => ∫ ω, max (F m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
