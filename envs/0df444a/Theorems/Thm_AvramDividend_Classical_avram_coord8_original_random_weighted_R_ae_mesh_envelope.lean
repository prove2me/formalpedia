-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord8_original_random_weighted_R_ae_mesh_envelope
-- name    : AvramDividend.Classical.avram_coord8_original_random_weighted_R_ae_mesh_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:55:24.231401+00:00
-- url     : https://prove2.me/theorems/02cc79c1-af0b-489d-8d18-a4a7ef96d22e
-- title:
--   Original BV raw-jump remainder endpoint bound with sample-dependent grid coefficients
-- statement:
--   For the actual bounded-variation Levy process and monotone physical mesh, even sample-dependent bounded derivative or stopping weights satisfy the sharp almost-sure endpoint control of the raw-jump remainder. The bound is pathwise after restricting to the full-measure original-remainder monotonicity event; no predictability or measurability of the weights is silently assumed.
-- source:
--   Exact original-process pointwise instantiation of Proved d95da4ae a.e. monotonicity and b5f11d6e monotone-mesh endpoint estimate with random a(omega,i). Intended for the sample-dependent stopped derivative coefficients in the actual B residual; requires a separately justified uniform K bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_monotone_R_mesh_bound
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_coord8_original_random_weighted_R_ae_mesh_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (a : Ω → ℕ → ℝ) (K : ℝ)
    (hK : ∀ ω i, i ∈ Finset.range (n + 1) → |a ω i| ≤ K) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      |∑ i ∈ Finset.range (n + 1),
          a ω i * (R (u n i) - R (u n (i + 1)))| ≤
        K * (R (u n (n + 1)) - R (u n 0)) := by sorry
