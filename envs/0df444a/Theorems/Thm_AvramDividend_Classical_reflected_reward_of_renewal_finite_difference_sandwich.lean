-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflected_reward_of_renewal_finite_difference_sandwich
-- name    : AvramDividend.Classical.reflected_reward_of_renewal_finite_difference_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:27:48.215275+00:00
-- url     : https://prove2.me/theorems/319da48e-fc97-4ddf-a4ce-e914fa9943e2
-- title:
--   Unique reflected regulator reward from two stopped-renewal finite-difference bounds
-- statement:
--   Let W be differentiable at a with nonzero derivative d. Suppose an extended nonnegative real stopped-reward value V is eventually bracketed, as ε decreases to zero from above, by the lower and upper finite differences ε W(a−ε)/(W(a)−W(a−ε)) and ε W(a+ε)/(W(a+ε)−W(a)), interpreted using ENNReal.ofReal. Then V equals ENNReal.ofReal(W(a)/d). This is the deterministic final squeeze from an eventual killed-reflected-record renewal bound to the barrierSupValue scale derivative ratio. The two stochastic reward bounds are explicit hypotheses and are not silently asserted.
-- source:
--   Proved Prove2Me renewal_scale_finite_difference_limits_of_hasDerivAt theorem ab77ec0b-a6b7-42e3-aaa3-14f0c49b5420; limits and order-topology squeeze. Application to Avram et al (2007), Proposition 1 reflected-supremum dividend value.

import Theorems.Thm_AvramDividend_Classical_renewal_scale_finite_difference_limits_of_hasDerivAt
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.reflected_reward_of_renewal_finite_difference_sandwich
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : d ≠ 0)
    (V : ℝ≥0∞)
    (hLo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal
        (ε * W (a - ε) / (W a - W (a - ε))) ≤ V)
    (hHi : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      V ≤ ENNReal.ofReal
        (ε * W (a + ε) / (W (a + ε) - W a))) :
    V = ENNReal.ofReal (W a / d) := by sorry
