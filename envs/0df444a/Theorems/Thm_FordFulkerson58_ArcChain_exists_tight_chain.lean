-- Prove2me | Theorems.Thm_FordFulkerson58_ArcChain_exists_tight_chain
-- name    : FordFulkerson58.ArcChain.exists_tight_chain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:34:36.570591+00:00
-- url     : https://prove2.me/theorems/e932d777-4b78-4581-a400-7ee7c1bbaa5c
-- title:
--   §3, p. 1780, the trace-back — final labels have a tight arc into every labeled non-source and a tight chain from S of length π_v
-- statement:
--   Let $N$ be a network with non-negative arc lengths $l_e$, let $S$ be a set of nodes, and let $\pi$ be a terminal labeling produced by the labeling process from the initial labels ($0$ on $S$, $\infty$ elsewhere). Let $v$ be a node with $\pi_v < \infty$. Then
--
--   1. if $v \notin S$, there is an arc $e$ traversable from some node $u$ to $v$ that is *tight*: $\pi_u + l_e = \pi_v$;
--   2. there are a node $u \in S$ and a chain $u = v_0 \xrightarrow{e_1} v_1 \to \cdots \xrightarrow{e_p} v_p = v$ all of whose arcs are tight,
--   $$\pi_{v_i} = \pi_{v_{i-1}} + l_{e_i} \quad (i = 1,\dots,p),$$
--   and whose length $\sum_i l_{e_i}$ equals $\pi_v$.
--
--   This is the trace-back step of §3: a shortest chain to a sink is recovered from the final labels by following tight arcs backwards.
--
--   **Formalization Note** The page says that following tight arcs backwards from $v$ "eventually" reaches $S$. With arcs of length $0$ that is not true of every backward walk: with $s \to a$ of length $1$ and $a \rightleftarrows b$ of length $0$, the final labels are $\pi_a = \pi_b = 1$, and the backward search may alternate between $a$ and $b$. The statement therefore asserts that *some* chain of tight arcs from $S$ reaches $v$, with length $\pi_v$, which is what the procedure needs.
-- source:
--   Ford and Fulkerson, A suggested computation for maximal multi-commodity network flows, Management Sci. 50(12S) (2004), p. 1780, §3 ("To find a chain from S to T of length π_k, look for an arc P_jP_k such that π_j + l_jk = π_k … traced out (in reverse)")

import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_Labeling

namespace FordFulkerson58.ArcChain

/-- §3, p. 1780, the trace-back: at the end of the labeling process (non-negative lengths), every node
`v ∉ S` with a finite label has a tight arc `e` into it (`lab u + l e = lab v`), and some chain from a
node of `S` to `v` consists of tight arcs and has length `lab v`. -/
theorem exists_tight_chain {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) (lab : V → WithTop ℝ)
    (hrun : Relation.ReflTransGen (RelaxStep N l) (initLabel S) lab) (hterm : IsTerminal N l lab)
    (v : V) (hv : lab v ≠ ⊤) :
    (v ∉ S → ∃ (e : E) (u : V), Traverses N e u v ∧ lab u + (l e : WithTop ℝ) = lab v) ∧
    ∃ u ∈ S, ∃ (p : List E) (vs : List V), IsChainWalk N u v p vs ∧
      (∀ (i : ℕ) (h : i < p.length), ∃ x y : V, vs[i]? = some x ∧ vs[i + 1]? = some y ∧
        lab y = lab x + (l p[i] : WithTop ℝ)) ∧
      ((chainLength l p.toFinset : ℝ) : WithTop ℝ) = lab v := by sorry

end FordFulkerson58.ArcChain
