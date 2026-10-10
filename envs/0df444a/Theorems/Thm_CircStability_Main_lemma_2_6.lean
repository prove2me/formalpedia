-- Prove2me | Theorems.Thm_CircStability_Main_lemma_2_6
-- name    : CircStability.Main.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:25.922919+00:00
-- url     : https://prove2.me/theorems/e91af46b-ae2c-463f-ae6e-78f20e2d95ec
-- title:
--   Lemma 2.6 — the (n+1)-closure preserves the length of a longest (x, y)-path
-- statement:
--   Let $G$ be a graph on $n$ vertices and let $\mathrm{cl}_{n+1}(G)$ be its $(n+1)$-closure. Then for any vertices $x,y$, the longest $(x,y)$-path in $\mathrm{cl}_{n+1}(G)$ has the same length as the longest $(x,y)$-path in $G$. Equivalently: for every $(x,y)$-path $P$ of $\mathrm{cl}_{n+1}(G)$ there is an $(x,y)$-path $Q$ of $G$ with
--
--   $$
--   |E(P)|\le|E(Q)|.
--   $$
--
--   Lemma 2.6 is the closure analogue of the Bondy–Chvátal closure lemma for Hamiltonian paths; it is the ingredient of Lemma 2.7.
--
--   **Formalization Note.** The statement is given in the one-sided form above. It is equivalent to equality of the longest path lengths, since $G\subseteq\mathrm{cl}_{n+1}(G)$ makes every path of $G$ a path of the closure; the form also covers pairs $x,y$ joined by no path. The graph is on an arbitrary finite vertex type with $n$ elements.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 9, Lemma 2.6

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
open Finset SimpleGraph

namespace CircStability.Main

theorem lemma_2_6 {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : Fintype.card V = n)
    (G : SimpleGraph V) (x y : V) (p : (kClosure (n + 1) G).Walk x y) (hp : p.IsPath) :
    ∃ q : G.Walk x y, q.IsPath ∧ p.length ≤ q.length := by sorry

end CircStability.Main
