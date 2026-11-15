-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a104_original_given_poisson_count_independent_physical_negative_mark_stream_20261114
-- name    : AvramDividend.Classical.avram_a104_original_given_poisson_count_independent_physical_negative_mark_stream_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T18:47:39.605814+00:00
-- url     : https://prove2.me/theorems/f21e965c-091e-4326-9642-d30498ff8204
-- title:
--   Given the original physical negative count Poisson law, construct its source-independent marked jump sequence with exact Laplace balance
-- statement:
--   With a concrete measurable same-original-space count K of negative physical jumps already proved to be Poisson of rate r and equal almost surely to the true full-negative jump count, construct measurable random marks Y_n independent of K, which reproduce the actual physical jump sum up to t, have the fixed-length exponential product moments, and whose marked exponent matches the original negative Levy measure. This isolates mark independence and chronologically sourced jumps from the separate count Poisson law, without postulating an independent auxiliary space.
-- source:
--   Same-source finite-activity marked Lévy jump process theorem; source count Poisson law provided as explicit assumptions by A20. Reuse Proved A96 original measurable physical jump times and marks, Proved A99 original active Dirac representation, and standard iid-mark conditional law of Poisson random measures.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a104_original_given_poisson_count_independent_physical_negative_mark_stream_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hK : Measurable K) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (hRate : (r : ℝ) =
      ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :
    ∃ (Y : ℕ → Ω → ℝ) (m : ℝ),
      (∀ n, Measurable (Y n)) ∧
      IndepFun K (fun ω n => Y n ω) P ∧
      (∀ᵐ ω ∂P, J ω = ∑ j ∈ Finset.range (K ω), Y j ω) ∧
      (∀ k : ℕ,
        (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) =
          m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by sorry
