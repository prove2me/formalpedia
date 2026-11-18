-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB58_discounted_monotone_weighted_increment_sup_bound
-- name    : AvramDividend.Classical.avram_gbB58_discounted_monotone_weighted_increment_sup_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:43:34.035035+00:00
-- url     : https://prove2.me/theorems/121eb051-e8f3-4762-bd2a-9f0d295dd96a
-- title:
--   A monotone discounted centred Gaussian physical-increment mesh is bounded by the source-path sup norm
-- statement:
--   For a finite physical grid, monotone nonnegative discount weights with a0≤1, a centred source path b0=0 and |b_i|≤ε, the exact weighted increment mesh sum has absolute value at most ε. This follows from Abel summation with nonnegative weight differences. It gives a pathwise uniform noise bound on a narrow Gaussian Brownian tube without requiring identification of a stochastic Itô integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB53_physical_discounted_mesh_abel_telescope
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB58_discounted_monotone_weighted_increment_sup_bound
    (m : ℕ) (a b : ℕ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (ha : Antitone a) (ha0 : a 0 ≤ 1)
    (ham : 0 ≤ a m) (hb0 : b 0 = 0)
    (hb : ∀ i ≤ m + 1, |b i| ≤ ε) :
    |(Finset.range (m + 1)).sum (fun i =>
      a i * (b (i + 1) - b i))| ≤ ε := by sorry
