-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_positive_increment_possible_at_every_time
-- name    : AvramDividend.Classical.unbounded_positive_increment_possible_at_every_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:12:38.685332+00:00
-- url     : https://prove2.me/theorems/9ecb74e2-b888-4efd-af02-8c97dbdbd43a
-- title:
--   An unbounded-variation spectrally negative Lévy process has positive increments with positive chance at every positive time
-- statement:
--   For a spectrally negative Lévy process of unbounded variation, any fixed strictly positive time admits positive increments with positive probability in the measure-theoretic sense that the event X_t ≤ 0 does not hold almost surely. This follows from eventual positivity of the Laplace exponent at a large nonnegative parameter, the Lévy exponential moment formula at time t, and monotonicity of expectation. It is a genuine unconditional stochastic step towards upward small-time regularity, but alone does not prove almost-sure positivity arbitrarily near zero, which additionally requires a path-event zero-one argument.
-- source:
--   Kyprianou, Kuznetsov and Rivero (2013), The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.1; accepted Prove2Me exponent growth theorem f06e514c-3654-4d25-b2f8-a5afce8580a7 and direct Laplace method from accepted 41b98039-640f-41c0-9a30-3f790be483bf.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_positive_increment_possible_at_every_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    ¬ (∀ᵐ ω ∂P, X.X t ω ≤ 0) := by sorry
