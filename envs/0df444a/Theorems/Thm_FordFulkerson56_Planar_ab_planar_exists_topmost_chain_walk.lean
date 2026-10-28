-- Prove2me | Theorems.Thm_FordFulkerson56_Planar_ab_planar_exists_topmost_chain_walk
-- name    : FordFulkerson56.Planar.ab_planar_exists_topmost_chain_walk
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-28T05:28:33.722108+00:00
-- url     : https://prove2.me/theorems/d5890d00-6ce2-4013-bd05-32e669c68128
-- title:
--   Proof of Theorem 2, p. 403 — existence of a top-most chain walk in an ab-planar network whose interleaved subchains must intersect
-- statement:
--   Let $N$ be a finite network with source $a$ and sink $b$ such that
--
--   1. no arc of $N$ joins $a$ and $b$ directly;
--   2. at least one chain joins $a$ and $b$;
--   3. $N$ is $ab$-planar (`Nonempty (ABPlaneDrawing N)`), i.e., the graph of $N$ together with an extra arc $ab$ can be drawn in the plane $\mathbb R^2$ without crossings.
--
--   Then there exists a chain walk $(p, vs)$ from $a$ to $b$ — the **top-most chain** $T$ joining $a$ and $b$ in the normalized plane drawing of Ford and Fulkerson (§2, p. 403) — such that for any two interior vertices $v_1 = vs[j_1]$ and $v_2 = vs[j_2]$ ordered along $vs$ with $0 < j_1 < j_2 < |vs| - 1$, every chain walk $(p_1, vs_1)$ from $v_1$ to $b$ and every chain walk $(p_2, vs_2)$ from $a$ to $v_2$ must share at least one vertex:
--
--   $$
--   \exists\, w \in V,\qquad w \in vs_1 \;\wedge\; w \in vs_2.
--   $$
--
--   This isolates the plane-topological step of the proof of Theorem 2 in Ford and Fulkerson (1956, p. 403): in a plane drawing normalized so that the arc $ab$ lies on the outer boundary and the network lies in the vertical strip between the vertical lines through $a$ and $b$ below $T$, the cycle $T \cup \{ab\}$ bounds the region containing the rest of the network, and two subchains inside that region whose endpoints $(a, v_2)$ and $(v_1, b)$ interleave along $T$ as $a < v_1 < v_2 < b$ must cross at a vertex.
--
--   **Formalization Note** The chain $T$ is presented explicitly via its arrangement `(p, vs)` satisfying `FordFulkerson56.MinCut.IsChainWalk N N.source N.sink p vs` so that the linear order of vertices from $a = vs[0]$ to $b = vs[|vs|-1]$ along $T$ is given directly by list indices $0 < j_1 < j_2 < |vs| - 1$.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 403, Proof of Theorem 2 (top-most chain and crossing of interleaved subchains)

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_Planar_ABPlaneDrawing

namespace FordFulkerson56.Planar

/-- Proof of Theorem 2, p. 403: in an ab-planar network `N` (with no arc joining `a` and `b` and
some chain joining `a` and `b`), there exists a "top-most" chain walk `(p, vs)` from `a` to `b`
such that for any two interior vertices `vs[j₁]` and `vs[j₂]` with `0 < j₁ < j₂ < vs.length - 1`,
any chain walk from `vs[j₁]` to `b` and any chain walk from `a` to `vs[j₂]` share a vertex. -/
theorem ab_planar_exists_topmost_chain_walk {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : FordFulkerson56.MinCut.Network V E)
    (hno_ab : ∀ e : E, ¬ ((N.tail e = N.source ∧ N.head e = N.sink) ∨
      (N.tail e = N.sink ∧ N.head e = N.source)))
    (hconn : ∃ C : Finset E, FordFulkerson56.MinCut.IsChain N N.source N.sink C)
    (hplanar : Nonempty (ABPlaneDrawing N)) :
    ∃ (p : List E) (vs : List V),
      FordFulkerson56.MinCut.IsChainWalk N N.source N.sink p vs ∧
      ∀ (j₁ j₂ : ℕ) (hj₁ : 0 < j₁) (hj₁₂ : j₁ < j₂) (hj₂ : j₂ + 1 < vs.length)
        (p₁ p₂ : List E) (vs₁ vs₂ : List V),
        FordFulkerson56.MinCut.IsChainWalk N (vs[j₁]'(by omega)) N.sink p₁ vs₁ →
        FordFulkerson56.MinCut.IsChainWalk N N.source (vs[j₂]'(by omega)) p₂ vs₂ →
        ∃ w ∈ vs₁, w ∈ vs₂ := by sorry

end FordFulkerson56.Planar
