-- Prove2me | Theorems.Thm_DirTeleMC_cheapest_jump
-- name    : DirTeleMC.cheapest_jump
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:21.667133+00:00
-- url     : https://prove2.me/theorems/d0609cd7-954f-4d62-8f17-9c5109545af2
-- title:
--   §B.4, p.21 — a minimum-weight walk is a cheapest jump
-- statement:
--   Let $\Gamma > 0$, $L$ a state, and $u, w$ vertices with $\mathrm{dist}(u, w) \le \theta$. Give each vertex $v$ the weight $e^{L(v)/\Gamma}(e^{1/\Gamma} - 1)$. Then:
--   1. for every path $P$, the increase $\Delta_L(P)$ equals the total weight of the vertices $P$ leaves;
--   2. some walk from $u$ to $w$ with at most $\theta$ arcs has minimum weight among all such walks (dynamic programming over the number of arcs finds one);
--   3. every minimum-weight such walk is a path;
--   4. every minimum-weight such walk minimizes $\Delta_L$ among the paths with at most $\theta$ arcs from $u$ to $w$ (it is a valid choice in line 6 of Algorithm 1), and its increase is at most that of every walk with at most $\theta$ arcs from $u$ to $w$.
--
--   Differences from the source:
--   - reading: dynamic programming over the number of arcs finds a minimum-weight walk → a minimum-weight walk with at most θ arcs exists; reason: the algorithmic content (time) is part of the running-time milestone
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §B.4 "Potential", p.21 (PDF p.22)

import Mathlib
import Definitions.Def_DirTeleMC_GreedyLoop

namespace DirTeleMC

/-- **The cheapest jump** (§B.4 "Potential").
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), §B.4, p.21: "For a path P, the increase ∆_L(P) is the total weight of the vertices of G that P leaves, where
a vertex v ∈ V has the weight e^{L(v)/Γ}(e^{1/Γ} − 1). So a path with at most θ arcs between two given vertices
of G that minimizes ∆_L(P) is a shortest path for these weights among paths with at most θ arcs. Dynamic
programming over the number of arcs finds a minimum-weight walk with at most θ arcs; as the weights are
positive, removing a cycle would lower its weight, so this walk is such a path. As e^{mx} − 1 ≥ m(e^x − 1) for
x > 0 and m ≥ 1, the increase of a walk is at least its weight, so this path is also a cheapest jump among all
walks."

For `Γ > 0`, a state `L` and vertices `u, w` with `dist(u, w) ≤ θ`:
1. for every path `P`, `Δ_L(P)` equals the weight of `P` (the sum of the weights of the vertices it leaves);
2. a walk with at most `θ` arcs from `u` to `w` of minimum weight exists;
3. every such minimum-weight walk is a path;
4. every such minimum-weight walk is a cheapest jump of line 6 of Algorithm 1 (it minimizes `Δ_L` among the
   paths with at most `θ` arcs from `u` to `w`), and its increase is at most that of every walk with at most `θ`
   arcs from `u` to `w`. -/
theorem cheapest_jump {n : ℕ} (adj : Fin n → Fin n → Bool) (θ : ℕ) (Γ : ℝ) (hΓ : 0 < Γ)
    (L : Fin n → ℕ) (u w : Fin n) (huw : HopReach adj θ u w) :
    (∀ P : List (Fin n), P.Nodup → incr Γ L (pathLoads P) = walkWeight Γ L P) ∧
    (∃ W, IsJump adj θ u w W ∧ ∀ W', IsJump adj θ u w W' → walkWeight Γ L W ≤ walkWeight Γ L W') ∧
    (∀ W, IsJump adj θ u w W → (∀ W', IsJump adj θ u w W' → walkWeight Γ L W ≤ walkWeight Γ L W') →
      W.Nodup) ∧
    (∀ W, IsJump adj θ u w W → (∀ W', IsJump adj θ u w W' → walkWeight Γ L W ≤ walkWeight Γ L W') →
      IsCheapest adj θ Γ L u w W ∧
        ∀ W', IsJump adj θ u w W' → incr Γ L (pathLoads W) ≤ incr Γ L (pathLoads W')) := by sorry

end DirTeleMC
