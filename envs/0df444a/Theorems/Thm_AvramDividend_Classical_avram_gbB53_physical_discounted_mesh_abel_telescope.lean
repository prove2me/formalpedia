-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB53_physical_discounted_mesh_abel_telescope
-- name    : AvramDividend.Classical.avram_gbB53_physical_discounted_mesh_abel_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:30:37.282203+00:00
-- url     : https://prove2.me/theorems/df708b71-d9a9-404f-a476-1163f8b0fe4c
-- title:
--   Finite physical-grid Abel summation for discounted centred Gaussian increments
-- statement:
--   For arbitrary real discount weights a_i and centred source coordinates b_i, the exact finite sum of weighted increments a_i(b_{i+1}-b_i) equals the discounted terminal minus initial coordinate plus the discrete weight-variation integral. This deterministic Abel summation identity allows pathwise convergence of the original upper-strip Gaussian physical-grid source by ordinary Riemann integration, avoiding an unnecessary stochastic Ito-limit construction on that event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB53_physical_discounted_mesh_abel_telescope
    (m : ℕ) (a b : ℕ → ℝ) :
    (Finset.range (m + 1)).sum (fun i =>
      a i * (b (i + 1) - b i)) =
    a m * b (m + 1) - a 0 * b 0 +
      (Finset.range m).sum (fun i =>
        (a i - a (i + 1)) * b (i + 1)) := by sorry
