-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_constructive_exact_arboricity
-- name    : ConstructiveArboricity.Exact.constructive_exact_arboricity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:50.151437+00:00
-- url     : https://prove2.me/theorems/6a2fc93e-582e-4fe2-ae39-8fb185c7a1e4
-- title:
--   Theorem 1 — Constructive exact arboricity
-- statement:
--   There is one fixed finite deterministic program $A$ that, for every finite simple unweighted undirected graph $G$ with $n$ vertices and $m$ edges, returns the exact arboricity $a(G)$ and a partition of every input edge into $a(G)$ forests. All isolated vertices are allowed, and an edgeless graph returns $a(G)=0$.
--
--   The same program satisfies both time bounds:
--
--   $$T_A(G)\le C_\varepsilon\min\{(n+2)^{2+\varepsilon},(m+2)^{4/3+\varepsilon}\}\qquad(\varepsilon>0).$$
--
--   For each positive $\varepsilon$, the positive constant $C_\varepsilon$ is independent of the graph. The program and its word-width constant are fixed before $\varepsilon$. It halts on every valid input and computes both the value and a color of every edge in input order. The width convention uses all $W$ above a fixed multiple of the binary length of $n+m+2$.
--
--   The input consists of $n,m$ and a sparse endpoint list. Isolated vertices and empty forest classes require no explicit per-vertex output. This retains the entire graph domain while allowing a bound expressed solely in $m$. The assertion is an algorithmic existence statement on an instruction interpreter; no correct or fast algorithm, partition, flow solver or claimed cost function occurs as a hypothesis.
--
--   Differences from the source:
--   - encoding: a finite simple undirected graph with its edge sets → vertices Fin n, edge identities Fin m, an injective unordered endpoint map, and color fibers; reason: every finite simple graph admits such labels; isolated vertices and empty color classes are retained
--   - reading: an algorithm on a graph, with empty forests and isolated vertices implicit → one deterministic finite word-RAM program with sparse endpoint-list input and edge-color-list output; reason: the source does not specify a machine or input layout; implicit isolated vertices permit the stated m-only bound without restricting graphs, and all machine execution is charged
--   - encoding: min{n^(2+o(1)), m^(4/3+o(1))} time → for every positive epsilon a graph-independent C_epsilon bounds the same program by C_epsilon min{(n+2)^(2+epsilon),(m+2)^(4/3+epsilon)}; reason: equivalent asymptotic exponents, with shifts absorbing finite-size conventions
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1476.pdf, Theorem 1, p.4; Algorithm 7 and proof pp.32–33

import Mathlib
import Definitions.Def_ConstructiveArboricity_Exact_Machine

namespace ConstructiveArboricity.Exact

/-- Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei,
Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027
submission #1476 (October 2026), Theorem 1, p.4; proof pp.32–33.
PDF sha256 9aa896d448cf63b4f502235eca19f59eb0468fad89783d21467b281518e3c512.
One finite program returns the minimum and a color for every input edge.
The sparse endpoint input keeps all isolated vertices implicitly; the shifts by
2 absorb only finite-size conventions. Both exponents hold for this same program. -/
theorem constructive_exact_arboricity :
    ∃ (P : Program) (b : ℕ), 0 < b ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
        ∀ (G : Graph) (W : ℕ), WidthEnough b (G.n + G.m) W →
          ∃ (t k : ℕ) (c : Fin G.m → Fin k),
            Runs P G.input (G.partitionOutput k c) W t ∧
            k = G.arboricity ∧ G.ForestPartition k c ∧
            (t : ℝ) ≤ C * min
              ((G.n + 2 : ℝ) ^ (2 + ε))
              ((G.m + 2 : ℝ) ^ ((4 : ℝ) / 3 + ε)) := by sorry

end ConstructiveArboricity.Exact
