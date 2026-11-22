-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_original_spatial_poisson_Nat_count_family_realisation
-- name    : AvramDividend.Classical.avram_a77_original_spatial_poisson_Nat_count_family_realisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:40:45.239236+00:00
-- url     : https://prove2.me/theorems/18038ff6-6d72-4a11-8198-7a04ffad668c
-- title:
--   Original disjoint spatial physical jump counts admit independent finite Poisson Nat representatives
-- statement:
--   For original X physical marked jump counts on a fixed finite time interval, given independent finite disjoint negative Borel mark counting measures and each exact original Poisson count marginal law, choose a finite family of measurable Nat-valued Poisson representatives preserving a.e. equality of each real physical count, their exact intensities, and joint independence. This transports independence through measurable ENNReal.toReal and Nat.floor and a.e. equality. It is the precise missing source-to-generic bridge for the connected finite-Borel physical Laplace identity.
-- source:
--   Proved original Borel Poisson count theorem a20, Open original spatial independence 3ece8183, accepted main a77 to 8bb to finite-simple source child c39bdceb; generic finite independent Poisson PGF theorem 200cd6c0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a77_original_spatial_poisson_Nat_count_family_realisation
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
    :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∃ (K : Fin n → Ω → ℕ) (r : Fin n → ℝ≥0),
      (∀ i, Measurable (K i)) ∧
      iIndepFun K P ∧
      (∀ i, HasLaw (K i) (poissonMeasure (r i)) P) ∧
      (∀ᵐ ω ∂P, ∀ i, (K i ω : ℝ) =
        (NX ω (Ioc 0 t ×ˢ B i)).toReal) ∧
      (∀ i, (r i : ℝ) =
        ((t : ℝ≥0∞) * X.ν (B i)).toReal) := by sorry
