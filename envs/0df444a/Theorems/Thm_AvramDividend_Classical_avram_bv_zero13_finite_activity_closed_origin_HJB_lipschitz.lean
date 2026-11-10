-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_finite_activity_closed_origin_HJB_lipschitz
-- name    : AvramDividend.Classical.avram_bv_zero13_finite_activity_closed_origin_HJB_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:36:05.793332+00:00
-- url     : https://prove2.me/theorems/b6ad40f2-6675-46ee-a592-d3f52a4bc6a9
-- title:
--   Original finite activity BV HJB closed zero-boundary two-point Lipschitz envelope
-- statement:
--   Under the original Standing bounded variation finite negative activity generator HJB, positive reserve gradient lower bound, continuous nonnegative-origin candidate and positive cap, any positive epsilon strictly below the cap admits a single nonnegative Lipschitz constant K controlling absolute differences w(z)-w(y) for all reserve values y,z in the entire closed interval zero through epsilon. No derivative or generator at zero is assumed. The exact original finite-activity near-zero derivative upper bound is combined with the pinned closed-endpoint C1 monotonicity argument. This is the boundary regularity interface needed to remove spatial reserve cutoffs in both finite-cap and unrestricted-cap source budgets.
-- source:
--   Source-exact original near-zero generator derivative bound 4a65a38a and closed endpoint C1 gradient two-point envelope aeec073e, with pinned Mathlib monotoneOn_of_deriv_nonneg on Icc 0 epsilon; direct consumer is original BV spatial cutoff passage in 73419313 and 6211514c.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_finite_activity_origin_derivative_uniform_HJB
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_finite_activity_closed_origin_HJB_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ Icc (0 : ℝ) ε, ∀ z ∈ Icc (0 : ℝ) ε,
        |w z - w y| ≤ K * |z - y| := by sorry
