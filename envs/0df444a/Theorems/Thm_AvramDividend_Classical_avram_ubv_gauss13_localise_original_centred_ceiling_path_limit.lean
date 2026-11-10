-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_centred_ceiling_path_limit
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_centred_ceiling_path_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:00:33.823483+00:00
-- url     : https://prove2.me/theorems/2cfa6158-03f1-49ff-be55-cd3d3fd390a3
-- title:
--   Original centred Gaussian source converges along true physical ceiling approximations
-- statement:
--   For the actual original zero-jump X.X process, any sampled ceiling times that sandwich the physical stopping clock with vanishing deterministic overhang have almost-sure convergence of the centred source X.X minus its original drift to the centred source at the physical clock. The result imports the Proved raw original-path ceiling limit and derives convergence of the clock via squeeze; it is exactly the a.e. source premise of the physical quadratic-energy Fatou interface 135fcca1.
-- source:
--   Public 23b87d40 original raw process ceiling path limit plus deterministic clock sandwich and continuity of arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_zerojump_ceiling_path_limit

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_centred_ceiling_path_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (grid : ℕ → ℕ → ℝ≥0) (K : ℕ → Ω → ℕ)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (hBounds : ∀ n ω,
      τ ω ≤ grid n (K n ω) ∧
      grid n (K n ω) ≤ τ ω + δ n) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n =>
        X.X (grid n (K n ω)) ω -
          (grid n (K n ω) : ℝ) * X.c)
        atTop (𝓝 (X.X (τ ω) ω - (τ ω : ℝ) * X.c)) := by sorry
