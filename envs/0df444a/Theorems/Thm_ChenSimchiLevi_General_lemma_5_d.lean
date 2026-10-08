-- Prove2me | Theorems.Thm_ChenSimchiLevi_General_lemma_5_d
-- name    : ChenSimchiLevi.General.lemma_5_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:11:34.650712+00:00
-- url     : https://prove2.me/theorems/59148577-aac4-4151-83ee-86c1af943a5a
-- title:
--   Lemma 5(d): structure of a coercive sym-$k$-convex function
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be continuous and symmetrically $k$-convex with $k\ge0$, and suppose $g(y)\to+\infty$ as $|y|\to\infty$. Then there are $s\le S$ such that $S$ minimizes $g$, $s$ is the least solution of $g(s)=g(S)+k$, every $y<s$ has $g(y)>g(s)$, and
--   $$g(y)\le g(z)+k\qquad\text{whenever}\quad (s+S)/2\le y\le z.$$
--   These thresholds locate the region in which a fixed-cost order can improve the inventory value.
-- source:
--   Chen, Simchi-Levi, Operations Research 52(6) (2004), p. 891, Lemma 5(d)

import Definitions.Def_ChenSimchiLevi_General_SymKConvex

set_option autoImplicit false

namespace ChenSimchiLevi.General

open Filter

/-- Lemma 5(d), p. 891. -/
theorem lemma_5_d (k : ℝ) (g : ℝ → ℝ) (hk : 0 ≤ k)
    (hg : SymKConvex k g) (hcont : Continuous g)
    (h₁ : Tendsto g atTop atTop) (h₂ : Tendsto g atBot atTop) :
    ∃ s S : ℝ, s ≤ S ∧ (∀ y, g S ≤ g y) ∧
      IsLeast {x | g x = g S + k} s ∧
      (∀ y < s, g s < g y) ∧
      ∀ y z, (s + S) / 2 ≤ y → y ≤ z → g y ≤ g z + k := by sorry

end ChenSimchiLevi.General
