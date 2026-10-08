-- Prove2me | Theorems.Thm_BellmanDP_GoldMining_finite_horizon_regions_stabilize
-- name    : BellmanDP.GoldMining.finite_horizon_regions_stabilize
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T15:14:14.371203+00:00
-- url     : https://prove2.me/theorems/be5328b0-f598-4636-b288-2d985afe8c6e
-- title:
--   Chapter II, Theorem 6 — the decision regions of $f_N$ converge monotonically and coincide with those of $f$ for $N \ge N_0$
-- statement:
--   Let $0 \le p_1, p_2 < 1$ and $0 \le r_1, r_2 \le 1$, let $f$ be the solution of (5.1) (bounded in every rectangle), and let $f_N$ be the $N$-stage returns of Theorem 5. For a value function $v$ with continuation $w$, the A-region is $\{(x,y) : x, y \ge 0,\ v(x,y) = p_1[r_1x + w((1-r_1)x,y)]\}$ and the B-region is defined in the same way with the B-branch. The regions of $f$ are those with $v = w = f$; the regions of $f_{N+1}$ are those with $v = f_{N+1}$, $w = f_N$. Then:
--   1. **Monotone convergence.** Either the A-regions of $f_N$ increase and the B-regions decrease for all $N \ge 1$, or the A-regions decrease and the B-regions increase for all $N \ge 1$.
--   2. **Finite stabilization.** There is an integer $N_0$ such that for every $N \ge N_0$ the A-region of $f_N$ equals the A-region of $f$ and the B-region of $f_N$ equals the B-region of $f$.
--
--   With Theorem 2, the second part says that for all large $N$ the $N$-stage process uses the same index rule as the unbounded process.
--
--   **Formalization Note** "Converge in a monotone fashion" is read as monotonicity of the regions (as sets) in $N$, in one of the two directions; which direction occurs depends on the parameters. The regions include ties, so a point on the separating line lies in both.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter II, § 12, Theorem 6, p. 74

import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 6, p. 74: for `0 ≤ p₁, p₂ < 1`,
`0 ≤ r₁, r₂ ≤ 1`, with `f` the solution of (5.1) (bounded in every rectangle), the decision
regions of `f_N` move monotonically in `N` (the A-regions increase and the B-regions decrease,
or the reverse, for all `N ≥ 1`), and there is `N₀` such that for `N ≥ N₀` the A- and B-regions
of `f_N` are identical with those of `f`. Index shift: the regions of `f_{N+1}` are
`regionA p₁ r₁ (goldIter … N) (goldIter … (N + 1))` and likewise for B. -/
theorem finite_horizon_regions_stabilize (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (f : ℝ → ℝ → ℝ) (hf : IsGoldMiningSolution p₁ p₂ r₁ r₂ f) (hfb : BoundedOnRectangles f) :
    ((∀ N : ℕ,
        regionA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ N) (goldIter p₁ p₂ r₁ r₂ (N + 1)) ⊆
          regionA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ (N + 1)) (goldIter p₁ p₂ r₁ r₂ (N + 2)) ∧
        regionB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ (N + 1)) (goldIter p₁ p₂ r₁ r₂ (N + 2)) ⊆
          regionB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ N) (goldIter p₁ p₂ r₁ r₂ (N + 1))) ∨
     (∀ N : ℕ,
        regionA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ (N + 1)) (goldIter p₁ p₂ r₁ r₂ (N + 2)) ⊆
          regionA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ N) (goldIter p₁ p₂ r₁ r₂ (N + 1)) ∧
        regionB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ N) (goldIter p₁ p₂ r₁ r₂ (N + 1)) ⊆
          regionB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ (N + 1)) (goldIter p₁ p₂ r₁ r₂ (N + 2)))) ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      regionA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ N) (goldIter p₁ p₂ r₁ r₂ (N + 1)) = regionA p₁ r₁ f f ∧
      regionB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ N) (goldIter p₁ p₂ r₁ r₂ (N + 1)) =
        regionB p₂ r₂ f f := by sorry

end BellmanDP.GoldMining
