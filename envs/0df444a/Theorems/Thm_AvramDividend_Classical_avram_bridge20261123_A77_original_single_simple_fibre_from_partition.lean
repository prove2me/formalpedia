-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_single_simple_fibre_from_partition
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_single_simple_fibre_from_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T16:27:51.941584+00:00
-- url     : https://prove2.me/theorems/6c3848ee-68e5-43f0-97d4-fbba852d1ccb
-- title:
--   One physical negative-mark SimpleFunc finite fibre, from the canonical Proved natural fibre partition
-- statement:
--   For one nonpositive finite-range real-valued simple mark function, given an exact finite disjoint natural enumeration of the negative Borel value fibres as guaranteed by Proved avram_a21_simple_mark_natural_fibre_partition, construct a measurable and almost surely nonpositive physical weighted jump-count random variable, prove its almost surely exact equality to the original pathwise finite actual negative-mark sum, and identify the original Levy intensity exponential rate as the finite sum over those same physical fibres.
-- source:
--   Exact original A77 physical fibre open theorem 5aaebfc3 and Proved natural fibre partition 80a945d2 (both canonical Prove2Me).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_single_simple_fibre_from_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hSupport :
      ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧
        J ω = ∑ u ∈ S,
          (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u))
    (hCountLaw : ∀ (B : Set ℝ), MeasurableSet B →
      B ⊆ Iio (0 : ℝ) →
      (let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 t ×ˢ B)
       ∃ (K : Ω → ℕ) (r : ℝ≥0),
         Measurable K ∧ HasLaw K (poissonMeasure r) P ∧
         (∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal) ∧
         (r : ℝ) = ((t : ℝ≥0∞) * X.ν B).toReal))
    (g : SimpleFunc ℝ ℝ)
    (hg : ∀ y, g y ≤ 0)
    (hPartition :
      ∃ (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ),
      (∀ i ∈ Finset.range K,
        MeasurableSet (B i) ∧ B i ⊆ Iio (0 : ℝ)) ∧
      (∀ i ∈ Finset.range K,
        ∀ j ∈ Finset.range K, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ w : ℝ → ℝ,
        (∑ i ∈ Finset.range K, w (c i)) = ∑ y ∈ g.range, w y) ∧
      (∀ i ∈ Finset.range K, B i = Iio (0 : ℝ) ∩ g ⁻¹' {c i})) :
    ∃ (f : Ω → ℝ) (r : ℝ),
      Measurable f ∧
      (∀ᵐ ω ∂P, f ω ≤ 0) ∧
      (∀ᵐ ω ∂P, ∀ (S : Finset ℝ≥0),
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) →
        f ω = ∑ u ∈ S,
          g (X.X u ω -
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)) ∧
      (r = (t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (g y) - 1 ∂X.ν)) ∧
      ∃ (k : ℕ) (B : Fin k → Set ℝ) (a : Fin k → ℝ),
        (∀ i, MeasurableSet (B i)) ∧
        (∀ i, B i ⊆ Iio (0 : ℝ)) ∧
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
        (∀ᵐ ω ∂P, f ω =
          ∑ i : Fin k, a i *
            (((Measure.count.restrict {u : ℝ≥0 |
                0 < u ∧ X.X u ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B i)).toReal) ∧
        r = ∑ i : Fin k,
          (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
            (Real.exp (a i) - 1) := by sorry
