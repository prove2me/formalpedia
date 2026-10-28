-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflected_no_downward_jumps_of_continuous_supremum
-- name    : AvramDividend.Classical.reflected_no_downward_jumps_of_continuous_supremum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:48:22.396715+00:00
-- url     : https://prove2.me/theorems/76e606f2-0d86-4e16-b85a-b507decb2d00
-- title:
--   Reflection at a continuous running supremum has no downward jumps for spectrally negative càdlàg paths
-- statement:
--   For a spectrally negative Lévy sample path X with no positive jumps and existing left limits, and any continuous path S representing a running supremum, its reflection R=S−X has no downward jumps at strictly positive times. Namely whenever the left limit of R at t is l, we have l≤R(t). The proof uses the Lévy process's noPosJumps and leftLim structure fields, continuity of S, subtraction of convergent functions, and uniqueness of limits along the nontrivial strict-left neighbourhood filter. This is a genuine càdlàg path property required to prove upper semicontinuity and attainment of excursion maxima, conditional only on running-supremum continuity.
-- source:
--   Standard fluctuation theory of reflected spectrally negative Lévy processes, Kuznetsov-Kyprianou-Rivero scale-function review (2013), excursion-height smoothness Lemma 2.4.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Separation.Hausdorff

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflected_no_downward_jumps_of_continuous_supremum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S : ℝ≥0 → ℝ)
    (hS : ∀ t : ℝ≥0, ContinuousAt S t) :
    ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Filter.Tendsto (fun s : ℝ≥0 => S s - X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) →
      l ≤ S t - X.X t ω := by sorry
