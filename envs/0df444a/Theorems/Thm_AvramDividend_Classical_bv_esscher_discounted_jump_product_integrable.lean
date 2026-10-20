-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_discounted_jump_product_integrable
-- name    : AvramDividend.Classical.bv_esscher_discounted_jump_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:26:55.069574+00:00
-- url     : https://prove2.me/theorems/6f255a67-682e-47a2-b208-36f23b1c58be
-- title:
--   Esscher discounted jump product is integrable in the bounded variation case
-- statement:
--   Deduce integrability of the Esscher discounted jump-magnitude exponential product from the Lévy bounded-variation integrability estimates at both Laplace arguments.
-- source:
--   Avram Palmowski Pistorius 2007 section 2; pinned Prove2Me integrability results.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_positive_magnitude_compensator_integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_discounted_jump_product_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (φ s : ℝ) (hφ : 0 ≤ φ) (hs : 0 ≤ s) :
    Integrable (fun z : ℝ≥0 =>
      Real.exp (-(φ * (z : ℝ))) *
        (1 - Real.exp (-(s * (z : ℝ)))))
      (X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by sorry
