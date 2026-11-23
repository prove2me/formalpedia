-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_count_independence_core
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_count_independence_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T17:27:52.540801+00:00
-- url     : https://prove2.me/theorems/db5c4c1b-30a8-4315-9750-6413a63e3ace
-- title:
--   Original Lévy disjoint negative-mark Borel count joint independence, Nat-valued finite-source core
-- statement:
--   Under the genuine original spectrally negative Levy process and finite negative Lévy intensity, for any disjoint finite Borel negative-mark family, every measurable Nat-valued representative of the actual physical Borel jump counts, equal almost surely in the real-count representation, forms a jointly independent family. This is the remaining original-space spatial Poisson splitting assertion. It must be derived from original Levy independent increments and marked-jump structure or a sound Levy-Ito point-process theorem; individual Poisson marginals or zero-event independence do not suffice.
-- source:
--   Original Avram source spatial independence 3ece8183, isolated after Proved original count-law Nat witness 1168da02 and finite-support exact ENNReal count correspondence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_count_independence_core
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
    iIndepFun K P := by sorry
