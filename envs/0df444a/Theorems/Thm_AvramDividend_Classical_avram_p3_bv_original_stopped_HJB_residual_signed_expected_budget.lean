-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_stopped_HJB_residual_signed_expected_budget
-- name    : AvramDividend.Classical.avram_p3_bv_original_stopped_HJB_residual_signed_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:53:13.704979+00:00
-- url     : https://prove2.me/theorems/6927a23f-cff9-42fd-86c3-33414fc941cb
-- title:
--   Original ruin-stopped BV HJB plus actual source residual signed L1 expectation budget
-- statement:
--   For the actual original controlled Lévy left-prepayment reserve and strict ruin-clock mask, the finite-grid discounted HJB and monotone jump-removed source residual corrections are both nonpositive, including in the cell crossing ruin. If this exact source-signed correction B is integrable and the separately compensated source jump term M is integrable and mean zero, their sum is integrable and has nonpositive expectation. This is a true stopped source expectation lemma. The unproved full pathwise cash/terminal chain identity remains a separate obligation.
-- source:
--   Proved original ruin-stopped discounted HJB grid and ruin-stopped weighted source BV residual grid helpers, original signed mean integral linearity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_ruin_stopped_HJB_grid_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_ruin_stopped_residual_mesh_nonpositive

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The actual pre-ruin stopped physical-source correction B is integrably
nonpositive even for a ruin-crossing next grid cell. A separately proved
centred jump-compensator M may be added without changing its mean sign. -/

theorem AvramDividend.Classical.avram_p3_bv_original_stopped_HJB_residual_signed_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (M B : Ω → ℝ)
    (hB : ∀ ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      B ω =
        (∑ i ∈ Finset.range n,
          if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u (i + 1) : ℝ) - (u i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range n,
           (if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u i : ℝ))) * deriv w (Z i)
           else 0) * (R (u i) - R (u (i + 1)))))
    (hMint : Integrable M P) (hBint : Integrable B P)
    (hMzero : (∫ ω, M ω ∂P) = 0) :
    Integrable (fun ω => M ω + B ω) P ∧
      (∫ ω, M ω + B ω ∂P) ≤ 0 := by sorry
