-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin15_original_same_space_gaussian_martingale_bracket_cross_public
-- name    : AvramDividend.Classical.avram_mix_fin15_original_same_space_gaussian_martingale_bracket_cross_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T13:05:41.591133+00:00
-- url     : https://prove2.me/theorems/ec7a2127-fa85-4ab1-85a8-32144fec7901
-- title:
--   Original mixed finite-activity intrinsic residual has Gaussian martingale bracket and orthogonal cross terms (public route)
-- statement:
--   Construct the Gaussian residual as the unique compact-uniform limit of the actual original finite-activity source truncations, on its unchanged Ω/P/right-continuous filtration. Establish almost-everywhere adaptedness, martingale conditional expectations, integrable squared values with bracket σ²t, and the zero mixed cross moment against the complementary original increment. The latter is claimed only under the integrable standing assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin15_original_same_space_gaussian_martingale_bracket_cross_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) ∧
      (∀ t : ℝ≥0,
        AEStronglyMeasurable[𝓕.rightCont t] (R t) P) ∧
      (∀ t : ℝ≥0, Integrable (R t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (R t) ω = R s ω) ∧
      (∀ t : ℝ≥0,
        Integrable (fun ω => (R t ω) ^ 2) P ∧
        (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        let cross : Ω → ℝ := fun ω =>
          (R t ω - R s ω) *
            ((X.X t ω - X.X s ω) - (R t ω - R s ω))
        Integrable cross P ∧ (∫ ω, cross ω ∂P) = 0) := by sorry
