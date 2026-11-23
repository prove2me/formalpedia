-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_count_all_atom_factorisation
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_count_all_atom_factorisation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T17:37:48.460931+00:00
-- url     : https://prove2.me/theorems/02c25d79-0072-4386-b54a-45e74c6d9f71
-- title:
--   Original spectrally negative Lévy physical disjoint negative-Borel count vectors: every point cylinder factors
-- statement:
--   For the unchanged source spectrally negative Levy process with finite negative Levy activity, any finite family of disjoint negative Borel sets, and simultaneous measurable Nat representatives of exact genuine physical marked count values, prove that every point-cylinder joint probability for the Nat count vector factors into the product of marginal point probabilities. This is the essential missing finite-dimensional spatial Poisson splitting law. A sound route must construct the original marked PRM or use a physical small-time marked grid collision/limit argument; the already proved one-set Poisson laws, empty-cell probabilities and time increment independence alone are insufficient.
-- source:
--   A77 actual spatial independence target 3ece8183 and Nat core db5c4c1b; pinned Mathlib finite Nat joint atom independence criterion, original actual Borel source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_count_all_atom_factorisation
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
    ∀ counts : Fin n → ℕ,
      P {ω : Ω | ∀ i, K i ω = counts i} =
        ∏ i : Fin n, P {ω : Ω | K i ω = counts i} := by sorry
