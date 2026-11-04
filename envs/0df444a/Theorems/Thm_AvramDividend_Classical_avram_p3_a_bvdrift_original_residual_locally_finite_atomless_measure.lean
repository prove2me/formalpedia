-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_residual_locally_finite_atomless_measure
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_residual_locally_finite_atomless_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:36:08.860167+00:00
-- url     : https://prove2.me/theorems/4f9a8a4a-d01b-48fb-b0a7-dc5aa1dbb96b
-- title:
--   Original BV physical drift residual has an atomless locally finite Stieltjes measure
-- statement:
--   Under the identical original spectrally negative bounded-variation Levy process and filtration, the physical drift residual after removing all actual negative left jumps induces one Stieltjes measure with exactly the residual increment masses on every (a,b], zero mass on all singletons, and finite mass on every finite ordered interval. This gives P3 a locally finite continuous Stieltjes integrator without an assumed decomposition identity.
-- source:
--   Uses the remote Accepted atomless original source residual measure theorem 14795a0f. Its interval masses are ENNReal.ofReal of a finite real difference, hence strictly below top by pinned Mathlib ENNReal.ofReal_lt_top.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_residual_locally_finite_atomless_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      (∀ a b : ℝ≥0, a ≤ b →
        μ (Ioc a b) = ENNReal.ofReal (
          ((((b : ℝ) * X.drift - X.X b ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
          (((a : ℝ) * X.drift - X.X a ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))))) ∧
      (∀ a : ℝ≥0, μ {a} = 0) ∧
      (∀ a b : ℝ≥0, a ≤ b → μ (Ioc a b) < ∞) := by sorry
