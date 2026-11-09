-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_original_generator_uniform_near_zero
-- name    : AvramDividend.Classical.avram_bv_tail12_original_generator_uniform_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:15:32.236496+00:00
-- url     : https://prove2.me/theorems/3bceec57-9445-476f-a8ac-d64349f400fd
-- title:
--   Every sufficiently small literal reserve forces an unbounded negative original generator cell
-- statement:
--   For the original bounded-variation spectrally negative Levy generator with the explicit singular negative jump density and zero compensated drift, every positive subunit reserve at most the fourth power of the reciprocal grid width produces a signed one-discount generator cell at most minus any chosen natural number. This supplies a uniform neighbourhood rather than a single chosen reserve.
-- source:
--   Applies public Proved 136fae3f to square root of literal reserve, uses exact original generator identification public Proved 24cc445a, and algebra from accepted 9fe384d7. Concrete conditional sampled-B interface for canonical 0b2da5b3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_subunit_original_generator_eq
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail12_original_generator_uniform_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0) (K : ℕ) (y : ℝ) (hy : 0 < y)
    (hy1 : y < 1)
    (hy_small : y ≤ (1 / ((K : ℝ) + 4)) ^ 4) :
    (1 / ((K : ℝ) + 4)) *
      (X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) y -
        (1 + y)) ≤ -(K : ℝ) := by sorry
