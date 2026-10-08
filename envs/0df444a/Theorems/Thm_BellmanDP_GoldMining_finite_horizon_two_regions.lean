-- Prove2me | Theorems.Thm_BellmanDP_GoldMining_finite_horizon_two_regions
-- name    : BellmanDP.GoldMining.finite_horizon_two_regions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T15:14:03.992194+00:00
-- url     : https://prove2.me/theorems/f16b4161-1b60-4994-904f-ca3d026a389a
-- title:
--   Chapter II, Theorem 5 — for each $N$ the $N$-stage process has two decision regions separated by a ray
-- statement:
--   Let $0 \le p_1, p_2 < 1$ and $0 \le r_1, r_2 \le 1$, and let $f_N$ be the $N$-stage returns
--   $$f_1(x,y) = \max\{p_1r_1x,\,p_2r_2y\},\qquad f_{N+1}(x,y) = \max\Bigl[A: p_1\bigl(r_1x + f_N((1-r_1)x,y)\bigr),\; B: p_2\bigl(r_2y + f_N(x,(1-r_2)y)\bigr)\Bigr].$$
--   Then for every $N \ge 1$ there is a ray through the origin in the closed quadrant, with direction $(u, v) \ne (0,0)$, $u, v \ge 0$, such that for all $x, y \ge 0$:
--   1. if $uy \le vx$ (the point lies on or below the ray), the A-choice is optimal for $f_N$ at $(x,y)$;
--   2. if $vx \le uy$ (on or above the ray), the B-choice is optimal for $f_N$ at $(x,y)$.
--
--   In words: for each $N$ there are exactly two decision regions, a sector along the $x$-axis where A is used and a sector along the $y$-axis where B is used. In the infinite process (Theorem 2) the separating ray is $p_1r_1x/(1-p_1) = p_2r_2y/(1-p_2)$; for finite $N$ it may differ.
--
--   **Formalization Note** The book states only "For each $N$, there are two decision regions". The statement above is the precise content its proof (pp. 72–74) establishes, using the homogeneity of $f_N$ in $(x, y)$. "The A-choice is optimal at $(x,y)$" means $f_N(x,y)$ equals the A-branch. The ray may be an axis ($u = 0$ or $v = 0$), in which case one region is the whole quadrant and the other the axis. The parameter ranges are those the chapter fixes in § 8 and in Theorem 2.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter II, § 12, Theorem 5, p. 72 (proof pp. 72-74)

import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 5, p. 72 ("For each N, there are two decision
regions"), in the precise form the proof (pp. 72–74) gives: for `0 ≤ p₁, p₂ < 1`,
`0 ≤ r₁, r₂ ≤ 1` and every `N ≥ 1`, there is a ray through the origin in the closed quadrant,
with direction `(u, v) ≠ 0`, `u, v ≥ 0`, such that the A-choice is optimal for `f_N` at every
point on or below the ray (`u y ≤ v x`) and the B-choice at every point on or above it
(`v x ≤ u y`). Here `f_N = goldIter … N`, written `N + 1` with `N : ℕ`. -/
theorem finite_horizon_two_regions (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1) (N : ℕ) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ (u ≠ 0 ∨ v ≠ 0) ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        (u * y ≤ v * x →
          goldIter p₁ p₂ r₁ r₂ (N + 1) x y = goldA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ N) x y) ∧
        (v * x ≤ u * y →
          goldIter p₁ p₂ r₁ r₂ (N + 1) x y = goldB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ N) x y) := by sorry

end BellmanDP.GoldMining
