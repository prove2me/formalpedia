-- Prove2me | Theorems.Thm_ExpanderBIS_HardCore_g2_connected_count
-- name    : ExpanderBIS.HardCore.g2_connected_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:19.793994+00:00
-- url     : https://prove2.me/theorems/84f0498e-24a4-45eb-9fbb-1605812d63b2
-- title:
--   §4.2, p. 21 — G² has at most (eΔ²)^t connected t-sets containing a given vertex
-- statement:
--   Let $G$ be a finite graph of maximum degree at most $\Delta$, with $\Delta \ge 1$. For every vertex $v$ and every $t \ge 0$, the number of $G^2$-connected sets $S$ with $v \in S$ and $|S| = t$ satisfies
--   $$\#\{S : v \in S,\ |S| = t,\ G^2[S] \text{ connected}\} \le (e\Delta^2)^t.$$
--
--   This is the instance, for the square graph $G^2$ (maximum degree at most $\Delta^2$), of the counting bound for connected induced subgraphs (Lemma 14 of the paper, cited from Galvin and Kahn). It bounds the number of polymers of each size through a vertex.
--
--   **Formalization Note** $\Delta \ge 1$ is needed: for $\Delta = 0$ the set $\{v\}$ is counted at $t = 1$ while $(e\cdot 0)^1 = 0$. The paper's setting has $\Delta \ge 3$. For $t = 0$ the left side is $0$, since a connected graph is nonempty.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 21, §4.2, "the number of G²-connected sets of size t containing vertex v is at most (eΔ²)^t" (Lemma 14, p. 16, applied to G²)

import Mathlib
import Definitions.Def_ExpanderBIS_HardCore_Setting

namespace ExpanderBIS.HardCore

open Finset

open Classical in
theorem g2_connected_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hΔ : 1 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) (t : ℕ) :
    (#(univ.filter (fun S : Finset V =>
        v ∈ S ∧ #S = t ∧ ((distLE G 2).induce (S : Set V)).Connected)) : ℝ)
      ≤ (Real.exp 1 * (Δ : ℝ) ^ 2) ^ t := by sorry

end ExpanderBIS.HardCore
