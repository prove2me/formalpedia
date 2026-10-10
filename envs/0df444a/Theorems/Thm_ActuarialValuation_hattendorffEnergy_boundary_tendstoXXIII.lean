-- Prove2me | Theorems.Thm_ActuarialValuation_hattendorffEnergy_boundary_tendstoXXIII
-- name    : ActuarialValuation.hattendorffEnergy_boundary_tendstoXXIII
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T23:05:57.833495+00:00
-- url     : https://prove2.me/theorems/5b704de2-b8a3-4bd1-b991-a9ae714726a7
-- title:
--   Vanishing quadratic boundary from summable annual energy
-- statement:
--   If a strictly positive survival-weight sequence tends to zero, a nonnegative annual energy series is summable, and every finite difference in an accumulated shock process satisfies its corresponding weighted energy inequality, then the survival-weighted squared accumulated shock tends to zero. This is the indispensable countable-lifetime boundary control in Hattendorff's theorem.
-- source:
--   Discrete weighted energy-tail and Cauchy inequality, derived for the countable-lifetime Hattendorff limit, independent of finite-terminal-age assumptions.

import Mathlib

namespace ActuarialValuation

theorem hattendorffEnergy_boundary_tendstoXXIII
    (S A a : ℕ → ℝ)
    (hS : ∀ n, 0 < S n)
    (hStendsto : Filter.Tendsto S Filter.atTop (nhds 0))
    (ha : Summable a) (han : ∀ n, 0 ≤ a n)
    (hEnergy : ∀ T N, T ≤ N →
      S N * (A N - A T) ^ 2 ≤ ∑ t ∈ Finset.Ico T N, a t) :
  Filter.Tendsto (fun N => S N * (A N) ^ 2) Filter.atTop (nhds 0) := by sorry

end ActuarialValuation
