-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva34_original_B_nonpositive_mean_of_full_integrable
-- name    : AvramDividend.Classical.avram_bva34_original_B_nonpositive_mean_of_full_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:41:45.021328+00:00
-- url     : https://prove2.me/theorems/f2807a9f-189b-4c23-a133-5c977363deac
-- title:
--   Integrable exact original BV uniform signed HJB generator-plus-residual has nonpositive expectation
-- statement:
--   For the literal stopped uniform BV physical HJB generator plus original Lévy drift/jump residual B on every physical grid, assume B_n is integrable. The already-Proved exact-source theorem avram_bv_residual9_original_B_positivepart_integrable_zero shows that its positive part has expectation zero. By pointwise B_n≤max(B_n,0) and monotonicity of expectation, the full original signed B_n has nonpositive mean for every n. The theorem does not assume or claim integrability of B without the explicit L1 hypothesis, so it remains mathematically sound also at infinite activity and infinite cap. It is directly reusable with finite-cap finite-activity source integrability bva33.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_B_positivepart_integrable_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva34_original_B_nonpositive_mean_of_full_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) :
    let B : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
       let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z i ∧ ENNReal.ofReal (Z i) < C then
           Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
          else 0) * (R (u n i) - R (u n (i + 1))))
    (∀ n, Integrable (B n) P) →
      ∀ n, (∫ ω, B n ω ∂P) ≤ 0 := by sorry
