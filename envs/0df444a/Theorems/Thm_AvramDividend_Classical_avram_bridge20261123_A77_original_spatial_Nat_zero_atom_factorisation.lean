-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_zero_atom_factorisation
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_zero_atom_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:43:08.865983+00:00
-- url     : https://prove2.me/theorems/22965098-6b8d-44e6-8289-fef35f3c2eb5
-- title:
--   Original Lévy finite negative-mark Borel count vector joint zero atom factors using Proved void product
-- statement:
--   For unchanged original physical source Lévy negative-mark jump counts, any finite disjoint Borel mark family, and Nat representatives a.e equal to the exact source counts, show that the probability all counts are zero is the product of their individual zero-count probabilities. Use Proved original finite disjoint negative-Borel mark void product, conversion of exact Nat/ENNReal count by Proved finite physical support, the measure-theoretic identity for zero measure of union, and almost-sure event measure congruence. This is the all-zero point of the true joint spatial count distribution.
-- source:
--   Proved Avram a27 original finite disjoint negative-Borel mark void product 286edb08, Proved 4ba72fb3 original exact source Nat counts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_zero_atom_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (K : Fin n → Ω → ℕ)
    (hK : ∀ i, Measurable (K i))
    (hReal : ∀ᵐ ω ∂P, ∀ i,
      (K i ω : ℝ) =
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B i)).toReal) :
    P {ω : Ω | ∀ i, K i ω = 0} =
      ∏ i : Fin n, P {ω : Ω | K i ω = 0} := by sorry
