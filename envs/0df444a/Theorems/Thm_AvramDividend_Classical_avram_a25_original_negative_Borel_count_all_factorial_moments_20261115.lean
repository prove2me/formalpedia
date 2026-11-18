-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_count_all_factorial_moments_20261115
-- name    : AvramDividend.Classical.avram_a25_original_negative_Borel_count_all_factorial_moments_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:18:42.965822+00:00
-- url     : https://prove2.me/theorems/84216278-a148-4bcd-b51a-7856399788f0
-- title:
--   Original physical negative Borel jump count has exact descending factorial moments of every order
-- statement:
--   For the genuine physical count of negative Borel-marked jumps of the specified original Lévy process and original P, the n-th descending factorial count moment is (T ν(B))^n for every n≥0. The previous original first moment and chronological pair moment results establish n=1 and n=2; prove all higher orders by iterated original marked compensator and chronological counting. This statement introduces no external Poisson driver or supplementary probability space.
-- source:
--   Existing original source count first and second factorial moment results 4faa7c77, 6d1258a3; iterate causal marked count compensation, keeping original P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_original_negative_Borel_count_all_factorial_moments_20261115
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal) :
    ∀ n : ℕ, (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n := by sorry
