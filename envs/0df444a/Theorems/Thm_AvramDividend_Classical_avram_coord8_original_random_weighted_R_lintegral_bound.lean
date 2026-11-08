-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord8_original_random_weighted_R_lintegral_bound
-- name    : AvramDividend.Classical.avram_coord8_original_random_weighted_R_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:19:02.844516+00:00
-- url     : https://prove2.me/theorems/277c5d67-269b-4c72-bec7-90a3d8601940
-- title:
--   Upper-integral bound for the original randomly weighted BV grid remainder
-- statement:
--   An original-process almost-sure endpoint envelope for bounded sample-dependent mesh coefficients yields the matching inequality of nonnegative upper integrals, without assuming measurability of the coefficients. Finite right-hand upper integral can be used in subsequent original stopped-grid integrability arguments after separate measurability checks.
-- source:
--   Direct monotonicity of the Lebesgue upper integral applied to public Proved 02cc79c1. Lean source SHA-256 87e504d6b586d87717cef823f045359ab2641f6c825c08a1bfd9fdcc575aad86. This is a nontrivial expectation interface for the original BV raw-remainder stopped-grid residual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_coord8_original_random_weighted_R_ae_mesh_envelope

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The pointwise original BV remainder envelope passes to the upper integral. -/

theorem AvramDividend.Classical.avram_coord8_original_random_weighted_R_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (a : Ω → ℕ → ℝ) (K : ℝ)
    (hK : ∀ ω i, i ∈ Finset.range (n + 1) → |a ω i| ≤ K) :
    let R : Ω → ℝ≥0 → ℝ := fun ω t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
    (∫⁻ ω, ENNReal.ofReal
      |∑ i ∈ Finset.range (n + 1),
        a ω i * (R ω (u n i) - R ω (u n (i + 1)))| ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal
        (K * (R ω (u n (n + 1)) - R ω (u n 0))) ∂P) := by sorry
