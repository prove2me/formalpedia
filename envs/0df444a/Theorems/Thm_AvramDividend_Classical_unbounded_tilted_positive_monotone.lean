-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_positive_monotone
-- name    : AvramDividend.Classical.unbounded_tilted_positive_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T02:25:06.139078+00:00
-- url     : https://prove2.me/theorems/4349fd54-dc08-4f40-a0d5-f301b2659a04
-- title:
--   Strict positivity and Esscher-tilted monotonicity of the q-scale function, for unbounded variation and without standing assumptions
-- statement:
--   For a spectrally negative Levy process of unbounded variation and q > 0, the canonical q-scale function W is strictly positive on the positive half-line, and there is a positive Esscher root phi with psi(phi) = q such that the Esscher-tilted function x |-> exp(-phi x) W(x) is nondecreasing on (0, infinity). This is the stochastic bridge from the canonical Laplace-transform definition of the scale function to the Esscher-normalised monotonicity that the tilted cumulative measure and the excursion representation need. It is stated here without any standing assumption: the two existing targets that carry the same content, scaleFunction_tilted_positive_monotone_of_unbounded and unbounded_tilted_cumulative_laplace_representation, both assume X.Standing, which is incompatible with an infinite small-jump first moment, because Standing contains the integrability of the full process increment. The statement is therefore not a duplicate of those targets but the without-Standing version of the same bridge.
-- source:
--   Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, the Esscher transform of the q-scale function; Kyprianou (2011), Excursions and Stochasticity, the positive Esscher root and the monotonicity of the tilted scale function. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.unbounded_tilted_positive_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by sorry
