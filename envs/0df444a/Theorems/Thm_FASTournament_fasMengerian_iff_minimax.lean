-- Prove2me | Theorems.Thm_FASTournament_fasMengerian_iff_minimax
-- name    : FASTournament.fasMengerian_iff_minimax
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:37.927245+00:00
-- url     : https://prove2.me/theorems/604c3a89-d755-4ca5-b9e7-d96bfdafc5e5
-- title:
--   Edmonds–Giles: FAS Mengerian iff $\lambda_w=\mu_w$ for every weight
-- statement:
--   Let $G=(V,A)$ be a finite digraph. Then $G$ is FAS Mengerian (the system $Nx\ge\mathbf 1,\ x\ge\mathbf 0$ is TDI, $N$ the FAS-arc incidence matrix) if and only if
--   $$
--   \lambda_w(G)=\mu_w(G)\qquad\text{for every } w\in\mathbb Z_+^A,
--   $$
--   i.e. for every nonnegative integral arc weighting, the maximum size of an FAS packing equals the minimum weight of a directed cycle.
--
--   This is the form in which FAS Mengerian is established in Section 3 (Lemma 3.2, Theorem 3.1).
--
--   **Formalization Note** $\lambda_w$ and $\mu_w$ take values in $\mathbb N\cup\{\infty\}$; both are $\infty$ on an acyclic digraph, where the system is TDI vacuously.
--
--   Differences from the source:
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
--   - encoding: N, the FAS-arc incidence matrix (rows: FASs) → rows indexed by all FASs F of G as finite arc sets; entry 1 if e ∈ F, else 0; reason: the same matrix up to the order of its rows
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
--   - encoding: λw(G), µw(G) (maximum / minimum) → lam G w, mu G w in ℕ∞, the supremum of FAS-packing sizes and the infimum of cycle weights; reason: both are ⊤ exactly when G has no directed cycle, where the source's maximum and minimum do not exist; otherwise they are the source's numbers
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, pp.3–4 ("by the aforementioned Edmonds-Giles theorem [19], G is FASM iff λw(G) = µw(G) for every nonnegative integral weight function w defined on A")

import Mathlib
import Definitions.Def_FASTournament_Arc
import Definitions.Def_FASTournament_FASMengerian
import Definitions.Def_FASTournament_lam
import Definitions.Def_FASTournament_mu

namespace FASTournament

/-- **FAS Mengerian ⇔ the packing–covering minimax `λ_w = µ_w` for every weight.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3–4: "Again, by the aforementioned Edmonds-Giles theorem [19], G is FASM iff
λw(G) = µw(G) for every nonnegative integral weight function w defined on A."

For every finite digraph `G`, `Nx ≥ 1, x ≥ 0` is TDI if and only if, for every weight
`w : A → ℤ₊`, the maximum size of an FAS packing equals the minimum weight of a directed cycle.

**Formalization Note.** `λ_w` and `µ_w` take values in `ℕ∞`; both are `⊤` on an acyclic digraph. -/
theorem fasMengerian_iff_minimax {V : Type*} [Fintype V] (G : Digraph V) :
    FASMengerian G ↔ ∀ w : Arc G → ℕ, lam G w = mu G w := by sorry

end FASTournament
