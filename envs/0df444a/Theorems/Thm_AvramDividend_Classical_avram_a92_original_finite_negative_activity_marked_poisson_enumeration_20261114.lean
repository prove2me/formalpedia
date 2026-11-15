-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a92_original_finite_negative_activity_marked_poisson_enumeration_20261114
-- name    : AvramDividend.Classical.avram_a92_original_finite_negative_activity_marked_poisson_enumeration_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T18:21:15.537287+00:00
-- url     : https://prove2.me/theorems/ed91ec27-7736-46ad-9324-fa933de5a78a
-- title:
--   Original finite negative Lévy activity: same-source Poisson count and independent marked sequence realise the physical jump sum
-- statement:
--   For a genuine finite-activity nonzero-negative-mark original spectrally negative Levy process, enumerate its actual jumps into an integer Poisson count N_t and a source-measurable infinite mark sequence Y that is independent of N_t. The physical negative-jump sum up to t equals the finite sum over those marks on a common conull event, each fixed-length exponential mark sum has kth power moment, and the Poisson count intensity times marked exponential excess equals the original negative Levy-mark cumulant. No auxiliary sample space or filtration augmentation is allowed.
-- source:
--   Physical Lévy jump measure is a Poisson random measure with intensity dt ν(dy); enumerating its jumps via the original marked path gives iid marks independent of counts. Proved A20 source Borel count first and second factorial moments, A85 integrability, A88 finite product, A89/A90 void probabilities, plus standard marked Poisson process theorem (Kyprianou / Protter).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a92_original_finite_negative_activity_marked_poisson_enumeration_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) :
    ∃ (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (r : ℝ≥0) (m : ℝ),
      Measurable N ∧ (∀ n, Measurable (Y n)) ∧
      IndepFun N (fun ω n => Y n ω) P ∧
      HasLaw N (poissonMeasure r) P ∧
      (∀ᵐ ω ∂P, J ω = ∑ j ∈ Finset.range (N ω), Y j ω) ∧
      (∀ k : ℕ,
        (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) =
          m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by sorry
