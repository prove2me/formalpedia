-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_tsum_of_quadratic_geometric_bound
-- name    : AvramDividend.Classical.continuousOn_tsum_of_quadratic_geometric_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:01:00.710999+00:00
-- url     : https://prove2.me/theorems/c03099b0-4964-4937-8f44-23c22fb758b1
-- title:
--   Quadratic-geometric uniform bound yields continuity of a renewal-density series
-- statement:
--   A family of real continuous functions with uniform quadratic-geometric majorant C n² ρ^n, for 0<ρ<1, has a continuous pointwise infinite sum. This directly matches the normalised BV renewal density bound n²(α/δ)^n/(δε). It follows from the Proved quadratic-exponential uniform M-test by r=−logρ.
-- source:
--   Weierstrass M-test via the previously Proved quadratic-exponential majorant theorem, with ρ^n=exp(−n(−logρ)).

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_continuousOn_tsum_of_quadratic_exp_bound
open AvramDividend.Classical Set

namespace AvramDividend.Classical
theorem continuousOn_tsum_of_quadratic_geometric_bound
    (f : ℕ → ℝ → ℝ) (K : Set ℝ) (C ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hf : ∀ n : ℕ, ContinuousOn (f n) K)
    (hbound : ∀ n : ℕ, ∀ x ∈ K,
      ‖f n x‖ ≤ C * ((n : ℝ) ^ 2 * ρ ^ n)) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, f n x) K := by sorry
end AvramDividend.Classical
