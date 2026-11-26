-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_approximate_reflection
-- name    : BellWilliams2001.ThresholdPolicy.approximate_reflection
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:45:28.123065+00:00
-- url     : https://prove2.me/theorems/290d8b1e-3fb0-5738-b365-5cbb3da859c3
-- title:
--   A bound for the one-dimensional Skorokhod regulator with positive slack
-- statement:
--   Let $x(0)=0$ and let $l$ be a continuous nondecreasing path starting at zero. Assume $x+l$ is nonnegative and $l$ is constant on each interval on which $x+l$ exceeds $\delta\ge0$. Then, whenever $x$ is bounded below on $[0,t]$,
--
--   $$-\inf_{0\le s\le t}x(s)\le l(t)\le -\inf_{0\le s\le t}x(s)+\delta.$$
--
--   Thus the regulator differs from the ordinary one-dimensional Skorokhod regulator by at most the slack in the condition on its increases.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, the perturbed Skorokhod comparison used in (163)

import Mathlib

open Set

namespace BellWilliams2001.ThresholdPolicy

theorem approximate_reflection (x l : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (δ : ℝ) (hδ : 0 ≤ δ)
    (hx₀ : x 0 = 0) (hx : BddBelow (Set.range (fun s : Set.Icc (0 : ℝ) t => x s)))
    (hl₀ : l 0 = 0) (hlc : ContinuousOn l (Set.Icc 0 t))
    (hlm : MonotoneOn l (Set.Icc 0 t))
    (hnon : ∀ s ∈ Set.Icc 0 t, 0 ≤ x s + l s)
    (hflat : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t →
      (∀ s ∈ Set.Ioc a b, δ < x s + l s) → l b = l a) :
    let v := -(⨅ s : Set.Icc (0 : ℝ) t, x s)
    v ≤ l t ∧ l t ≤ v + δ := by sorry

end BellWilliams2001.ThresholdPolicy
