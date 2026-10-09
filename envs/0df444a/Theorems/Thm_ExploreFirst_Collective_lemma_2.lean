-- Prove2me | Theorems.Thm_ExploreFirst_Collective_lemma_2
-- name    : ExploreFirst.Collective.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:02:49.601346+00:00
-- url     : https://prove2.me/theorems/1b29144d-c458-41d4-9225-8224b86273bb
-- title:
--   Lemma 2, p. 14 — $(x-\alpha)^2\le\beta x$ implies $x\le\alpha+\beta+\sqrt{\alpha\beta}$
-- statement:
--   Let $x\in\mathbb R$ and let $\alpha\ge0$ and $\beta\ge0$. If
--   $$(x-\alpha)^2\le\beta x,$$
--   then
--   $$x\le\alpha+\beta+\sqrt{\alpha\beta}.$$
--
--   This elementary bound on the larger root of a quadratic converts the Pinsker-type inequality of the proof of Theorem 4 into the explicit upper bound (14) on the fraction of pulls of the optimal arms.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 14, Lemma 2

import Mathlib

namespace ExploreFirst.Collective

/-- Lemma 2, p. 14: if `(x - α)² ≤ β x` with `α ≥ 0` and `β ≥ 0`, then `x ≤ α + β + √(αβ)`. -/
theorem lemma_2 (x α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (h : (x - α) ^ 2 ≤ β * x) :
    x ≤ α + β + Real.sqrt (α * β) := by sorry

end ExploreFirst.Collective
