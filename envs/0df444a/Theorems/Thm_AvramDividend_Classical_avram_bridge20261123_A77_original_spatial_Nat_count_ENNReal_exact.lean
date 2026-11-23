-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_count_ENNReal_exact
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_count_ENNReal_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:26:55.185076+00:00
-- url     : https://prove2.me/theorems/4ba72fb3-acf2-4a58-9f06-d5b5f0b216b3
-- title:
--   Original finite-activity marked Poisson Nat count representatives equal the full physical ENNReal counts almost surely
-- statement:
--   For the original finite-negative-activity Levy process and any finite family of Borel negative mark sets, each measurable Nat-valued Poisson count representative identified by the original A20 one-set theorem agrees as an ENNReal value with the genuine original marked jump count almost surely. Prove by applying Proved original A26 finite marked support and A27 exact Borel count equals filtered finite-support cardinality. The original full physical jump measure is retained, and no spatial independence is assumed.
-- source:
--   Original Avram A77 spatial independence target 3ece8183; A20 Poisson count law 54bd238b; A26 finite support efd5b548; A27 physical count equals card 11e24cb0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_count_ENNReal_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
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
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      (K i ω : ℝ≥0∞) =
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B i) := by sorry
