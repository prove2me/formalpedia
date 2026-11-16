-- Prove2me | Theorems.Thm_EuclidKSteiner_Supplement_theorem_1_2
-- name    : EuclidKSteiner.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:58:08.178047+00:00
-- url     : https://prove2.me/theorems/caceb5bb-f3cc-4b16-9c4c-8651dfe027a1
-- title:
--   Theorem 1.2 (Integer edge weights) — a minimum-weight tree spanning $P$ with at most $b$ Steiner edges in $2^{O(b)}(|G|+W)^{O(1)}$ time
-- statement:
--   Let $G$ be a loopless graph on $V(G)=\{0,\dots,n_V-1\}$ with edge set $E$ and edge weights that are integers in $[0,W]$. Let $P\subseteq V(G)$ be a terminal set with $G[P]$ connected, let $Q=V(G)\setminus P$ be the candidates, and let $b\ge0$ be an integer. A **feasible tree** is a tree $T\subseteq E$ whose vertex set contains $P$ and which has at most $b$ edges incident to the selected candidates (the vertices of $T$ outside $P$).
--
--   **Theorem.** There are a deterministic real-RAM program and a constant $C>0$ such that, on every such input, the program halts after $t$ steps with
--   $$t+1\le C\cdot 2^{C b}\cdot(|V(G)|+|E(G)|+W+2)^{C}$$
--   and outputs a feasible tree $T$ of minimum total weight among all feasible trees.
--
--   This is the integer-weight counterpart of Theorem 1.1 on abstract graphs: the time is single-exponential in the budget $b$ of Steiner edges and polynomial in the graph size and the largest weight, so the problem is fixed-parameter tractable for polynomially bounded weights.
--
--   **Formalization Note** The real RAM is the published `MatMulTimeLP.RealRAM` restricted by `FewInnerTSP.Admissible` (rational literals, no random draws, square roots allowed), as in the published goal. The input is `budgetLayout` (counts, terminal flags, edges with weights); the output is the edge list of $T$. $W$ is any upper bound on the edge weights.
--
--   Differences from the source:
--   - reading: "with G[P] connected" → $P\neq\emptyset$ and any two terminals are joined inside $G[P]$; reason: the standard convention that a connected graph is nonempty; for $V(G)=\emptyset$ no tree spans $P$ otherwise.
--   - encoding: "2^{O(b)}(|G| + W)^{O(1)} time" → one constant $C$, chosen with the program before the input, with $t+1\le C\,2^{Cb}(|V|+|E|+W+2)^C$ for every bound $W$ on the weights; reason: the meaning of the $O(\cdot)$ bounds; $+2$ only keeps the base at least $2$.
--   - encoding: "time" → steps of the published admissible real RAM, as in the published Theorem 1.1; reason: the paper states its running times in the real-RAM model (p.3).
--   - encoding: graph and weights → vertices $\{0,\dots,n_V-1\}$, a loopless edge set listed once, real weights that are nonnegative integers; the output is the edge list of $T$; reason: input/output representation; same instances.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Theorem 1.2, p.3 (PDF p.5); proof pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_EuclidKSteiner_Instance
import Definitions.Def_EuclidKSteiner_Layouts
import Definitions.Def_EuclidKSteiner_Supplement_IntWeightSteiner

set_option autoImplicit false

namespace EuclidKSteiner

namespace Supplement

/-- **Theorem 1.2 (Integer edge weights).** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized
Tractability of Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…),
Theorem 1.2, p.3 (PDF p.5); proved pp.19–20 (PDF pp.21–22): "Let G be a graph with integer edge
weights in [0, W], a terminal set P, and a candidate set Q = V(G) \ P, with G[P] connected. Given a
nonnegative integer b, a minimum-weight tree spanning P, with at most b edges in total incident to the
selected candidates, can be found deterministically in 2^{O(b)}(|G| + W)^{O(1)} time."

There are an admissible real-RAM program and a constant `C > 0` such that for every loopless graph
`G` on the vertices `0, …, nV − 1` with edge set `E` (listed once by `Ls`) and nonnegative integer
edge weights, every terminal set `P` with `G[P]` connected, every budget `b ≥ 0` and every tape, the
run on `budgetLayout` halts at a step `t` with `t + 1 ≤ C · 2^{C·b} · (nV + |E| + W + 2)^C` for every
`W` bounding the edge weights, and outputs (as an edge list) a tree `T` of `G` whose vertex set
contains `P`, with at most `b` edges incident to candidates, of minimum weight among all such trees.

**Formalization Note**
* Machine: `MatMulTimeLP.RealRAM` restricted by `FewInnerTSP.Admissible`, as in the published goal
  `EuclidKSteiner.theorem_1_1` ("We state our algorithmic running times in the real-RAM model", p.3).
* `|G| = |V(G)| + |E(G)|`; `W` is any upper bound on the weights (the time is polynomial in `W`, not
  in `log W`); `+ 2` keeps the base at least `2`.
* The output is the list of the tree's edges (`encodeEdgeList`), each edge once. -/
theorem theorem_1_2 :
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (nV : ℕ) (E : Finset (Sym2 (Fin nV))) (Ls : List (Fin nV × Fin nV)),
      IsEdgeListing Ls E → (∀ e ∈ E, ¬ e.IsDiag) →
      ∀ w : Sym2 (Fin nV) → ℝ, (∀ e ∈ E, ∃ z : ℕ, w e = (z : ℝ)) →
      ∀ P : Finset (Fin nV), InducedConnected E P →
      ∀ (b : ℕ) (ω : MatMulTimeLP.Tape), ∃ t : ℕ,
        MatMulTimeLP.HaltsAt A (budgetLayout P w Ls b) ω t ∧
        (∀ W : ℕ, (∀ e ∈ E, w e ≤ (W : ℝ)) →
          (t : ℝ) + 1 ≤ C * (2 : ℝ) ^ (C * b) * ((nV + E.card + W : ℝ) + 2) ^ C) ∧
        ∃ (T : Finset (Sym2 (Fin nV))) (L : List (Fin nV × Fin nV)), IsEdgeListing L T ∧
          OutputIs A (budgetLayout P w Ls b) ω t (encodeEdgeList L) ∧
          IsBudgetTree E P b T ∧
          ∀ T' : Finset (Sym2 (Fin nV)), IsBudgetTree E P b T' → edgeSum w T ≤ edgeSum w T' := by sorry

end Supplement

end EuclidKSteiner
