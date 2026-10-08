-- Prove2me | Theorems.Thm_EmmonsTardiness_EDD_convex_exchange_condition
-- name    : EmmonsTardiness.EDD.convex_exchange_condition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:28:06.922496+00:00
-- url     : https://prove2.me/theorems/8e56b2af-cb04-4c3d-b61f-781cae13bbec
-- title:
--   p. 713 — sufficient conditions ΔT_j ≥ ΔT_k and T_jb ≥ T_ka for Δg(T_j) ≥ Δg(T_k), g convex nondecreasing
-- statement:
--   Let $g$ be convex and nondecreasing on $[0,\infty)$. When two jobs $J_j$ and $J_k$ are interchanged, the tardiness of $J_j$ decreases from $T_{jb}$ (before) to $T_{ja}$ (after) and the tardiness of $J_k$ increases from $T_{kb}$ to $T_{ka}$, all four values being nonnegative. If
--
--   1. $\Delta T_j \ge \Delta T_k$, i.e. $T_{ka}-T_{kb}\le T_{jb}-T_{ja}$, and
--   2. $T_{jb}\ge T_{ka}$,
--
--   then the decrease in the penalty of $J_j$ is at least the increase in the penalty of $J_k$:
--   $$g(T_{ka})-g(T_{kb})\;\le\; g(T_{jb})-g(T_{ja}).$$
--
--   The second condition ensures that the decrease of $T_j$ happens over a part of the curve of $g$ that is at least as steep as the part over which $T_k$ increases. This is the comparison that lets the interchange and postponement arguments for total tardiness be carried over to the objective $\sum_J g(T_i)$.
--
--   **Formalization Note** The paper writes $\Delta T_i = |T_{ib}-T_{ia}|$; the Lean statement fixes the directions instead ($T_{ja}\le T_{jb}$, the decrease in $T_j$; $T_{kb}\le T_{ka}$, the increase in $T_k$), as the page's sentence describes, because with absolute values condition (1) could hold with both changes in the wrong direction. The paper's "to exceed" is read as "at least" (ties accepted, as in Theorem 1). Convexity and monotonicity are assumed only on $[0,\infty)$.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, p. 713, §Sequencing to minimize Σ_J g(T_i), where g is convex and increasing, first paragraph, third and fourth sentences (see Fig. 3, p. 714)

import Mathlib

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 713: sufficient conditions (1) `ΔT_j ≥ ΔT_k` and (2) `T_jb ≥ T_ka` for the
decrease `g(T_jb) - g(T_ja)` of the penalty of `J_j` to be at least the increase
`g(T_ka) - g(T_kb)` of the penalty of `J_k`, for `g` convex and nondecreasing on `[0, ∞)`. -/
theorem convex_exchange_condition (g : ℝ → ℝ)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (Tjb Tja Tkb Tka : ℝ)
    (hTja : 0 ≤ Tja) (hj : Tja ≤ Tjb) (hTkb : 0 ≤ Tkb) (hk : Tkb ≤ Tka)
    (h1 : Tka - Tkb ≤ Tjb - Tja) (h2 : Tka ≤ Tjb) :
    g Tka - g Tkb ≤ g Tjb - g Tja := by sorry

end EmmonsTardiness.EDD
