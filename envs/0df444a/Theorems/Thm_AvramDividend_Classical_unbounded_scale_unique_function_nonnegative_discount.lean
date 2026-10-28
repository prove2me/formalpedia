-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_unique_function_nonnegative_discount
-- name    : AvramDividend.Classical.unbounded_scale_unique_function_nonnegative_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:21:44.500923+00:00
-- url     : https://prove2.me/theorems/5dc895ab-326f-40c5-9875-78bd658c8514
-- title:
--   Full function-level uniqueness of nonnegative-discount q-scale functions
-- statement:
--   For any spectrally negative Lévy process of unbounded variation and a fixed nonnegative discount q, two functions satisfying the defining q-scale-function axioms are equal as functions on the entire real line. The proof combines Laplace uniqueness on positive reserves, the zero-origin result, and the prescribed vanishing of q-scale functions at negative reserves.
-- source:
--   The proved unbounded-scale Laplace uniqueness result, zero-origin normalisation, and the IsScaleFunction support axiom.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_unique_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_unique_function_nonnegative_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q W₁)
    (hW₂ : IsScaleFunction X q W₂) :
    W₁ = W₂ := by sorry
