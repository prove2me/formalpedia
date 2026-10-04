-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
-- name    : AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_bv
-- status  : Open
-- author  : @WillR
-- created : 2026-10-03T20:31:28.997232+00:00
-- url     : https://prove2.me/theorems/1c7b629b-b0e0-42c9-a71f-f01447c9a4a3
-- title:
--   Positive tilted scale function for a bounded-variation spectrally negative Lévy process
-- statement:
--   For a spectrally negative Lévy process under Standing and with bounded variation, its q-scale function is strictly positive at every positive reserve and can be normalised by a positive exponential to become nondecreasing. The positive renewal kernel K(x)=q+ν((-∞,-x)) with drift δ>0 yields the valid exponent q/δ. This case requires renewal-resolvent inversion and positive measure arguments, not merely algebra.
-- source:
--   Avram Palmowski Pistorius (2007), condition (3.3); Kuznetsov Kyprianou Rivero (2012), bounded-variation scale-function renewal formula; local research 07_BV_TILTED_MONOTONICITY.md

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Bounded-variation case of the stochastic scale-function bridge.
The positive renewal kernel gives monotonicity without an Esscher measure. -/
theorem scaleFunction_tilted_positive_monotone_of_bv {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  sorry

end AvramDividend.Classical
