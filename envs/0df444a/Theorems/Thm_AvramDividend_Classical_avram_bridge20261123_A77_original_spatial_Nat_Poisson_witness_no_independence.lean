-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_Poisson_witness_no_independence
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_Poisson_witness_no_independence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:17:53.745851+00:00
-- url     : https://prove2.me/theorems/1168da02-9bec-4d05-8b20-5613f570c189
-- title:
--   Original finite spatial negative-Borel Poisson count Nat representatives, no independence assumption
-- statement:
--   For the unchanged original spectrally negative Levy process with finite negative Levy intensity, construct for any finite family of disjoint measurable negative mark sets a measurable Nat-valued Poisson random variable for each exact original spatial source count, with correct intensity and almost-sure agreement. This finite indexed simultaneous representation uses only already Proved one-mark original source Poisson count laws and does not assume or assert spatial independence.
-- source:
--   Original Avram A77 spatial count independence frontier 3ece8183 and proved A20 original negative-Borel count Poisson law 54bd238b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_Poisson_witness_no_independence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∃ (K : Fin n → Ω → ℕ) (r : Fin n → ℝ≥0),
      (∀ i, Measurable (K i)) ∧
      (∀ i, HasLaw (K i) (poissonMeasure (r i)) P) ∧
      (∀ᵐ ω ∂P, ∀ i, (K i ω : ℝ) =
        (NX ω (Ioc 0 t ×ˢ B i)).toReal) ∧
      (∀ i, (r i : ℝ) =
        ((t : ℝ≥0∞) * X.ν (B i)).toReal) := by sorry
