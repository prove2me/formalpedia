-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_generic_original_chronological_pairs_monotone_grid_lintegral
-- name    : AvramDividend.Classical.avram_a20_generic_original_chronological_pairs_monotone_grid_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:34:11.5332+00:00
-- url     : https://prove2.me/theorems/fd4c3ff8-45d0-4caa-80e2-c537c28d447e
-- title:
--   Arbitrary finite physical chronological pair expectation from monotone exhaustive marked grids
-- statement:
--   For any finite-set-valued source marked times F on its original measurable probability space and measurable monotonically increasing finite-grid subsets G_m of chronological pairs which eventually exhaust all ordered pairs in F, the original expected full chronological pair cardinal in extended nonnegative reals equals the supremum of the exact finite-grid pair expectations. The proof uses cardinal monotonicity, eventual equality, and Mathlib monotone convergence for lintegral. This strips the negative-cutoff-specific assumption from an already Proved finite-band theorem and permits the genuine arbitrary Borel original Lévy pair expectation to close from its Borel finite-grid sources.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_generic_original_chronological_pairs_monotone_grid_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F : Ω → Finset ℝ≥0)
    (G : ℕ → Ω → Finset (ℝ≥0 × ℝ≥0))
    (hSub : ∀ m ω, G m ω ⊆
      (F ω ×ˢ F ω).filter (fun p => p.1 < p.2))
    (hMono : ∀ m k, m ≤ k → ∀ ω, G m ω ⊆ G k ω)
    (hStop : ∀ ω, ∃ N, ∀ m ≥ N,
      G m ω = (F ω ×ˢ F ω).filter (fun p => p.1 < p.2))
    (hMeas : ∀ m, Measurable
      (fun ω => ((G m ω).card : ℝ≥0∞)))
    (A : ℕ → ℝ≥0∞)
    (hMean : ∀ m, (∫⁻ ω, ((G m ω).card : ℝ≥0∞) ∂P) = A m) :
    (∫⁻ ω, (((F ω ×ˢ F ω).filter
      (fun p => p.1 < p.2)).card : ℝ≥0∞) ∂P) =
      ⨆ m, A m := by sorry
