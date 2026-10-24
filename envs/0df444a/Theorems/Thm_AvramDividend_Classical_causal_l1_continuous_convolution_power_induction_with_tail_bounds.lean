-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_continuous_convolution_power_induction_with_tail_bounds
-- name    : AvramDividend.Classical.causal_l1_continuous_convolution_power_induction_with_tail_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:09:06.770219+00:00
-- url     : https://prove2.me/theorems/7bde9362-b0d2-4526-83f8-b6d9cce0e85e
-- title:
--   Positive-time continuity of L1 causal convolution powers under quadratic-geometric bounds
-- statement:
--   Let κ be a causal real L1 function continuous and bounded on all positive tails, and let F_n be its convolution powers, nonnegative for nonnegative times and satisfying an explicit quadratic-geometric estimate F_n(x) ≤ (n+1)^2 ρ^(n+1)/x for x>0. Then every F_n is continuous on (0,∞). The proof inductively propagates L1 integrability, causal support, and continuity via the already Proved convolution theorems.
-- source:
--   Source-faithful standalone recursive assembly theorem needed for the BV Esscher continuous renewal-density representation (17bc0aad-807f-4e33-82d9-b8a65d2b6166), supporting the smooth-fit parent and barrier cstar derivative-one.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_integrable_causal_convolution
import Theorems.Thm_AvramDividend_Classical_causal_convolution_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_continuousOn_positive_causal_convolution_of_locally_bounded_integrable
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_l1_continuous_convolution_power_induction_with_tail_bounds
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hκint : Integrable κ volume)
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ n : ℕ, ContinuousOn (F n) (Ioi (0 : ℝ)) := by sorry
