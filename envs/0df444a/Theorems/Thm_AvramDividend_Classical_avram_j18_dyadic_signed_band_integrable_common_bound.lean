-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_j18_dyadic_signed_band_integrable_common_bound
-- name    : AvramDividend.Classical.avram_j18_dyadic_signed_band_integrable_common_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T18:29:33.835577+00:00
-- url     : https://prove2.me/theorems/7c33c081-8f9c-4d3c-9abe-44dca98b08ff
-- title:
--   Original finite-activity dyadic signed-band sums admit an integrable common envelope
-- statement:
--   For every original finite-activity negative band and deterministic physical interval, all dyadic finite-cell signed compensated counts are bounded by one P-integrable random variable. The bound follows from the original real marked-count L1 estimate 3d8bb7f8 and finite intensity ν(B), using disjoint cells and |left endpoint|≤1.
-- source:
--   The explicit domination half of Open ebfd1029; keeps the identical original-space dyadic marked count and compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_j18_dyadic_signed_band_integrable_common_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      ∃ bound : Ω → ℝ, Integrable bound P ∧
        (∀ k, ∀ᵐ ω ∂P, ‖M k ω‖ ≤ bound ω) := by sorry
