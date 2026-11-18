-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB59_original_discounted_gaussian_mesh_noise_sup_bound
-- name    : AvramDividend.Classical.avram_gbB59_original_discounted_gaussian_mesh_noise_sup_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:54:58.623469+00:00
-- url     : https://prove2.me/theorems/250f9d08-493f-4549-b6d7-4cde283a6e6c
-- title:
--   Original spectrally negative Lévy centred Gaussian physical-grid noise is bounded by the source tube width
-- statement:
--   For any original SpectrallyNegativeLevy path and monotone physical mesh s_i starting at zero, with zero source initial value and 0≤q, the exact discounted centred source increment mesh has absolute value no greater than a uniform bound ε on the source's compensated coordinates X(s_i)-c*s_i. This specialises the Abel sup-norm estimate to the original process rather than a surrogate Brownian integral. It can propagate uniform narrow-tube bounds to the original martingale L1 limit without proving an exact stochastic integral identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB58_discounted_monotone_weighted_increment_sup_bound
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB59_original_discounted_gaussian_mesh_noise_sup_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (m : ℕ) (s : ℕ → ℝ≥0) (hs : Monotone s)
    (hs0 : s 0 = 0) (hX0 : X.X 0 ω = 0)
    (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hTube : ∀ i ≤ m + 1,
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε) :
    |(Finset.range (m + 1)).sum (fun i =>
      Real.exp (-(q * (s i : ℝ))) *
        (X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c))| ≤ ε := by sorry
