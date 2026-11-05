-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_subtype_comap_integral_from_real_test
-- name    : AvramDividend.Classical.avram_p2_a_assist_subtype_comap_integral_from_real_test
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:42:17.494147+00:00
-- url     : https://prove2.me/theorems/d56f4c6e-d515-46ad-8246-c71a95424a67
-- title:
--   Negative subtype comap integral equals supported original real integral
-- statement:
--   An arbitrary real measure's negative-subtype comap integration against a real test equals integration of an ambient real test that agrees on negative values and whose topological support is strictly negative. This is a reusable measure-theoretic bridge from the original marked Lévy measure to Radon test uniqueness.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic
open MeasureTheory Set Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_a_assist_subtype_comap_integral_from_real_test
    (μ : Measure ℝ)
    (f : {x : ℝ // x < 0} → ℝ)
    (g : ℝ → ℝ)
    (hgsupp : tsupport g ⊆ Iio (0 : ℝ))
    (hagree : ∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x) :
    (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) μ)) =
      (∫ y, g y ∂μ) := by sorry
