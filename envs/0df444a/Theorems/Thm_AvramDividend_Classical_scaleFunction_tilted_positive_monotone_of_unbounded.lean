-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_unbounded
-- name    : AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_unbounded
-- status  : Open
-- author  : @WillR
-- created : 2026-10-03T20:31:31.533779+00:00
-- url     : https://prove2.me/theorems/85a4bf8b-5b82-4479-8c27-057fce34bffa
-- title:
--   Positive tilted scale function for a non-bounded-variation spectrally negative Lévy process
-- statement:
--   For a spectrally negative Lévy process under Standing and without bounded variation, its q-scale function is positive and has an exponentially normalised monotone form. This case covers both a positive Gaussian coefficient and infinitely active small jumps. It requires a Wiener–Hopf/descending ladder potential or equivalent fluctuation identity; the bounded-variation renewal proof is insufficient.
-- source:
--   Kuznetsov Kyprianou Rivero (2012), The Theory of Scale Functions for Spectrally Negative Lévy Processes, Esscher and Wiener–Hopf identities

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Non-bounded-variation case of the stochastic scale-function bridge,
requiring a Wiener–Hopf, Esscher or ladder-potential argument. -/
theorem scaleFunction_tilted_positive_monotone_of_unbounded {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : ¬ X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  sorry

end AvramDividend.Classical
