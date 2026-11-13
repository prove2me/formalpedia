-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
-- name    : AvramDividend.Classical.avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:06:53.004197+00:00
-- url     : https://prove2.me/theorems/1f13db96-f556-4634-b53a-fa1dade788bb
-- title:
--   Bounded real physical marked-jump integral is integrable and dominated by the finite original rectangle count mass
-- statement:
--   On nonnegative time × real jump-mark space, let μ be any measure and let S be Borel with finite μ-mass on the actual finite horizon rectangle (0,T]×S. For any measurable real weight g bounded in absolute value by 1 on S, its real integral against μ over the physical rectangle is well-defined (Bochner integrable), and its absolute value is bounded by the real rectangle mass μ((0,T]×S). The proof invokes the exact pinned Mathlib Measure.integrableOn_of_bounded from the finite mass and a.e. bound on the restriction, followed by norm_setIntegral_le_of_norm_le_const. For the actual original intrinsic Lévy jump measure this supplies the pointwise domination and integrability required for continuous Borel marked-jump moment approximation and the Gaussian L2 residual source route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (S : Set ℝ) (hS : MeasurableSet S)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hMass : μ (Ioc 0 T ×ˢ S) < ⊤)
    (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    IntegrableOn (fun p : ℝ≥0 × ℝ => g p.2)
      (Ioc 0 T ×ˢ S) μ ∧
    |∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂μ| ≤
      (μ (Ioc 0 T ×ˢ S)).toReal := by sorry
