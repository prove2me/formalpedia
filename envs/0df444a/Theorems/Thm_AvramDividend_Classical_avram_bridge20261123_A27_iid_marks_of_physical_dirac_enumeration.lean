-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A27_iid_marks_of_physical_dirac_enumeration
-- name    : AvramDividend.Classical.avram_bridge20261123_A27_iid_marks_of_physical_dirac_enumeration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T15:55:45.072794+00:00
-- url     : https://prove2.me/theorems/b5118988-977e-46a4-90c5-0dba73f98077
-- title:
--   Original Lévy same-space IID marks from its exact measurable physical Dirac jump enumeration
-- statement:
--   On the original probability space, assume the physical negative-jump random measure has an exact measurable countable Dirac enumeration, the conclusion of the already Proved A99 theorem. Establish a chronological IID negative-mark sequence, independent of the original finite-horizon physical Poisson count, matching the physical jump sum and normalized Lévy exponent. This isolates the remaining probabilistic marking theorem from the proved measurable enumeration.
-- source:
--   Original A27 physical iid mark source 952497f7; proved exact physical jump-measure Dirac enumeration A99 a348fc62; same pinned Avram structure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A27_iid_marks_of_physical_dirac_enumeration
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
      ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal)
    (hDirac : ∃ (T : ℕ → Ω → ℝ≥0) (A : ℕ → Set Ω)
      (Y : ℕ → Ω → ℝ),
      (∀ n, Measurable (T n)) ∧
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n, Measurable (Y n)) ∧
      (∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
        Measure.sum (fun n => (A n).indicator
          (fun _ => Measure.dirac (T n ω, Y n ω)) ω))) :
    ∃ (Y : ℕ → Ω → ℝ) (m : ℝ),
      (∀ n, Measurable (Y n)) ∧
      IndepFun K (fun ω n => Y n ω) P ∧
      iIndepFun Y P ∧
      (∀ n : ℕ, IdentDistrib (Y n) (Y 0) P P) ∧
      (∀ᵐ ω ∂P, J ω = ∑ j ∈ Finset.range (K ω), Y j ω) ∧
      (∀ k : ℕ,
        (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) =
          m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by sorry
