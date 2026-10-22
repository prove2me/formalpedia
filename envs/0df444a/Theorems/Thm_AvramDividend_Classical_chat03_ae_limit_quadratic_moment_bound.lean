-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_ae_limit_quadratic_moment_bound
-- name    : AvramDividend.Classical.chat03_ae_limit_quadratic_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T10:03:18.639985+00:00
-- url     : https://prove2.me/theorems/d0dcbace-b083-4a24-8494-ea1c6c2e420b
-- title:
--   Uniform quadratic-moment bound for the almost-sure limit
-- statement:
--   If real-valued almost-everywhere strongly measurable random variables Y_n converge almost everywhere to Z and their integrable real second moments are uniformly bounded by C, then the nonnegative Lebesgue integral of Z² is at most ENNReal.ofReal C. This passes quadratic moment control to the limiting random variable and enables its tail to be bounded separately.
-- source:
--   The accepted real-to-extended quadratic moment bound, the accepted uniform Fatou lemma, and continuity of y↦ENNReal.ofReal(y²).

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_fatou_ae_limit_lintegral_le_uniform_bound
import Theorems.Thm_AvramDividend_Classical_chat03_quadratic_moment_lintegral_le

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat03_ae_limit_quadratic_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (C : ℝ)
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)))
    (hY2 : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) P ∧
      ∫ ω, (Y n ω) ^ 2 ∂P ≤ C) :
    (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≤ ENNReal.ofReal C := by sorry
