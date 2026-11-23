-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_original_negative_Borel_step_approximants
-- name    : AvramDividend.Classical.avram_a77_original_negative_Borel_step_approximants
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:18:50.859134+00:00
-- url     : https://prove2.me/theorems/cc5c4242-c242-4a71-bac2-623c4399147e
-- title:
--   Original finite-activity negative-mark Borel step approximants with simultaneous physical and intensity Laplace limits
-- statement:
--   Given a finite set of original physical jump times before t with J equal to their actual signed jump sum, and original measurable Poisson Nat representatives for all negative Borel mark counts, construct measurable random exponents f_n and real deterministic intensity exponents r_n, each represented almost everywhere by a finite disjoint negative-Borel marked count partition. The f_n are nonpositive a.e. and converge a.e. to theta times the actual source signed J; the r_n converge to the correct t times original Lévy measure integral of exp(theta*y)-1. This isolates the genuine source finite-mark quantisation and two convergence obligations left in the accepted Avram a77->8bb->5b branch. It does not assume the desired final Laplace expectation identity.
-- source:
--   Original Avram full physical marked negative jump Laplace limit 5b48325d, using Proved a77 finite support pathwise ce005 and Proved original Borel Poisson count law a20. Actual source marked NX, same sample measure, no synthetic process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_a77_original_negative_Borel_step_approximants
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
    :
    ∃ (f : ℕ → Ω → ℝ) (r : ℕ → ℝ),
      (∀ n, Measurable (f n)) ∧
      (∀ᵐ ω ∂P, ∀ n, f n ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (θ * J ω))) ∧
      Tendsto r atTop (𝓝 ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν))) ∧
      ∀ n : ℕ, ∃ (k : ℕ) (B : Fin k → Set ℝ) (a : Fin k → ℝ),
        (∀ i, MeasurableSet (B i)) ∧
        (∀ i, B i ⊆ Iio (0 : ℝ)) ∧
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
        (∀ᵐ ω ∂P, f n ω =
          ∑ i : Fin k, a i *
            (((Measure.count.restrict {u : ℝ≥0 |
                0 < u ∧ X.X u ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B i)).toReal) ∧
        r n = ∑ i : Fin k,
          (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
            (Real.exp (a i) - 1) := by sorry
