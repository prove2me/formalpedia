-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_esscher_excursion_package
-- name    : AvramDividend.Classical.scaleFunction_esscher_excursion_package
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T13:54:21.197589+00:00
-- url     : https://prove2.me/theorems/dfdd9892-ffc0-40d6-abda-99c937e8291b
-- title:
--   Esscher-excursion derivative representation for the q-scale function under Condition (3.3)
-- statement:
--   Let W be the q-scale function of a standing spectrally negative Lévy process with q>0 and Condition (3.3). Under the Esscher transform at φ=Φ(q)>0, the zero-scale function has logarithmic derivative equal to the tail of the reflected-process excursion-height measure. Equivalently there is a positive excursion-height measure η, atomless under Condition (3.3), with finite tails above every positive level, such that W'(x)=(φ+η([x,∞)))W(x) for x>0. The q-scale function is strictly positive on the positive half-line. This source-specific theorem isolates the fluctuation/excursion content needed both for C1 regularity and Esscher-normalised monotonicity; all subsequent continuity and calculus steps are generic Mathlib.
-- source:
--   Avram–Palmowski–Pistorius (2007), condition (3.3) and scale-function regularity; Kuznetsov–Kyprianou–Rivero (2012), Esscher transform and excursion representation of scale functions; Chan–Kyprianou–Savov (2011), atomlessness/smoothness criteria for scale functions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_esscher_excursion_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ (φ : ℝ) (η : Measure ℝ),
        0 < φ ∧
        (∀ x : ℝ, η {x} = 0) ∧
        (∀ x : ℝ, 0 < x → η (Ici x) ≠ ⊤) ∧
        (∀ x : ℝ, 0 < x →
          HasDerivAt W ((φ + η.real (Ici x)) * W x) x) := by sorry
