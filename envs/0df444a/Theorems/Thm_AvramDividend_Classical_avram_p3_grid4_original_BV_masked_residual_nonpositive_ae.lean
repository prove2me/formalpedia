-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_BV_masked_residual_nonpositive_ae
-- name    : AvramDividend.Classical.avram_p3_grid4_original_BV_masked_residual_nonpositive_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:33:22.6273+00:00
-- url     : https://prove2.me/theorems/c9008c92-7551-4646-a19a-ace4c63ba7da
-- title:
--   Original BV source residual contributes nonpositively on every masked physical grid
-- statement:
--   For the actual original bounded-variation spectrally negative Levy process, the raw drift minus X.X minus exact all-jump tsum defines an almost-sure continuous monotone residual. Hence every nonnegative weighted sum of residual increments R(u_i)-R(u_{i+1}) on an arbitrary nondecreasing physical grid is almost surely nonpositive, including strict stopped-cell generator and gradient masks; no uniform L1 or zero-residual assertion is assumed. This closes the sign part of the second literal B summand in the c1e2f021 original source route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_BV_masked_residual_nonpositive_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ),
      Monotone u → (∀ i, 0 ≤ a i) →
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
      (∑ i ∈ Finset.range n, a i *
        (R (u i) - R (u (i + 1)))) ≤ 0 := by sorry
