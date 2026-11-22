-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_original_finite_negative_Borel_simple_laplace_from_counts
-- name    : AvramDividend.Classical.avram_a77_original_finite_negative_Borel_simple_laplace_from_counts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:33:19.720582+00:00
-- url     : https://prove2.me/theorems/c39bdceb-738d-4fd3-a69d-a20327e9ed68
-- title:
--   Original finite disjoint negative Borel physical jump count simple-mark Laplace identity
-- statement:
--   Given the original source physical marked-jump measure, complete finite-family spatial mark independence, and exact Poisson marginal laws for all negative Borel sets, the exponential of a finite disjoint weighted mark count has the product-Poisson Laplace formula. Counts are the actual X jumps. This follows from independent Poisson finite product transform plus the true a.e. Poisson-count representatives. Crucial finite partition step for the accepted Avram a77→8bb chain.
-- source:
--   Avram a77 original marked jump Laplace, 8bbaf3a8 child with original hJoint,hCountLaw; use generic finite independent Poisson transform lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a77_original_finite_negative_Borel_simple_laplace_from_counts
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0)
    (hJoint : ∀ (n : ℕ) (B : Fin n → Set ℝ),
      (∀ i, MeasurableSet (B i)) →
      (∀ i, B i ⊆ Iio (0 : ℝ)) →
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      iIndepFun (fun i : Fin n => fun ω : Ω =>
        NX ω (Ioc 0 t ×ˢ B i)) P)
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
    (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (a : Fin n → ℝ) :
    (∫ ω, Real.exp (∑ i : Fin n,
        a i *
          (((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc 0 t ×ˢ B i)).toReal) ∂P) =
      Real.exp (∑ i : Fin n,
        (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
          (Real.exp (a i) - 1)) := by sorry
