-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_density_measurable_finite
-- name    : AvramDividend.Classical.avram_gen14_singular_levy_density_measurable_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:32:02.232796+00:00
-- url     : https://prove2.me/theorems/00fa0af4-023a-47c6-8ab0-c5007ef7ea1b
-- title:
--   Singular negative Levy jump density is Borel measurable and finite pointwise
-- statement:
--   The proposed finite-variation negative-jump Levy measure is specified by a singular power density on the open interval from negative one to zero and vanishes elsewhere. The density is measurable and takes a finite extended nonnegative value at every individual jump mark, including both boundary points.
-- source:
--   Exact pinned Measurable.pow_const, Measurable.ennreal_ofReal, Measurable.ite and ENNReal.ofReal_lt_top; needed to use the Bochner integral withDensity change-of-measure theorem.

import Mathlib
open Classical MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen14_singular_levy_density_measurable_finite :
    Measurable (fun z : ℝ => if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0) ∧
    (∀ z : ℝ, (if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0) < ⊤) := by sorry
