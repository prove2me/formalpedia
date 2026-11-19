-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_sameX_intrinsic_gaussian_and_smallmark_limits_simultaneously_unique
-- name    : AvramDividend.Classical.avram_ja18_original_sameX_intrinsic_gaussian_and_smallmark_limits_simultaneously_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:49:30.411722+00:00
-- url     : https://prove2.me/theorems/cbc2e535-b0f0-4df1-b6db-27050ddeedfa
-- title:
--   Original same-Levy intrinsic Gaussian and compensated smallmark source limits are uniquely defined on one conull set
-- statement:
--   Two realisations R,S of the original same-X Gaussian truncated-residual limit and two realisations J,K of its actual compensated small-negative-mark limit coincide on a single common conull set at every time. This source uniqueness makes it valid to transfer integrability, adaptedness, martingale properties and physical mesh laws from a Proved canonical original source to the arbitrary limit witnesses quantified in the mixed two-noise B219 ledger, without replacing them by synthetic process witnesses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_sameX_intrinsic_gaussian_and_smallmark_limits_simultaneously_unique
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R S J K : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (nhds (R t ω)))
    (hS : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (nhds (S t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (nhds (J t ω)))
    (hK : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (nhds (K t ω))) :
    ∀ᵐ ω ∂P, (∀ t : ℝ≥0, R t ω = S t ω) ∧
               (∀ t : ℝ≥0, J t ω = K t ω) := by sorry
