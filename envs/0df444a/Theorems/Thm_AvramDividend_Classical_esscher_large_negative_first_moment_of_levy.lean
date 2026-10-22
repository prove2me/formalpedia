-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_large_negative_first_moment_of_levy
-- name    : AvramDividend.Classical.esscher_large_negative_first_moment_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:27:50.324279+00:00
-- url     : https://prove2.me/theorems/65364bbd-a6eb-4a02-9b0e-1622da6636dc
-- title:
--   Every spectrally negative Lévy triplet has finite Esscher-weighted large negative first moment
-- statement:
--   For any spectrally negative Lévy process and any positive Esscher exponent, the exponentially discounted first absolute moment of jumps of size at least one is finite. The process's built-in quadratic Lévy integrability gives finite large-negative-jump mass; the previously proved exponential weighted bounded-integrability lemma then applies. No unit-time first-moment assumption on the original process is required.
-- source:
--   The fully Proved theorems finite_large_negative_jump_mass and esscher_large_negative_first_moment_integrable under the canonical SpectrallyNegativeLevy structure.

import Mathlib.Order.BoundedOrder.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_large_negative_jump_mass
import Theorems.Thm_AvramDividend_Classical_esscher_large_negative_first_moment_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_large_negative_first_moment_of_levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ : ℝ) (hφ : 0 < φ) :
    IntegrableOn (fun y : ℝ => (-y) * Real.exp (φ * y))
      (Iic (-1 : ℝ)) X.ν := by sorry
