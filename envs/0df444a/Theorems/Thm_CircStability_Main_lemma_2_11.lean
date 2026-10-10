-- Prove2me | Theorems.Thm_CircStability_Main_lemma_2_11
-- name    : CircStability.Main.lemma_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:30.972493+00:00
-- url     : https://prove2.me/theorems/7ac3bceb-1d74-40cf-867c-d236d95146a6
-- title:
--   Lemma 2.11 — a (c+1)-closed non-Hamiltonian-connected G_c with δ ≥ 2 and e(G_c) > h(c+1, ⌊c/2⌋ − p) has one of two low-degree structures
-- statement:
--   Let $G_c$ be a graph on $c$ vertices with minimum degree at least $2$. Suppose $G_c$ is $(c+1)$-closed, is not Hamiltonian-connected, and
--
--   $$
--   e(G_c)>h\big(c+1,\lfloor c/2\rfloor-p\big)\quad\text{for some integer }p\ge0 .
--   $$
--
--   Then one of the following holds:
--   1. $G_c$ contains a set $S$ of $s-1$ vertices of degree at most $s$, where $2\le s\le\lfloor c/2\rfloor-p-1$, such that $G_c-S$ is a clique; or
--   2. $G_c$ contains a set $T$ of $t-1$ vertices of degree at most $t$, where $\lfloor c/2\rfloor-p+1\le t\le\lfloor c/2\rfloor$.
--
--   With $p=1$ this is the case distinction at the start of the proof of Theorem 4.1: alternative 2 becomes "$\lfloor c/2\rfloor-1$ vertices of degree at most $\lfloor c/2\rfloor$" (Lemma 4.2), alternative 1 the clique case (Lemma 4.3).
--
--   **Formalization Note.** $p$ ranges over $\mathbb N$ and all bounds are computed in $\mathbb N$. They are exact for $p<\lfloor c/2\rfloor$. For $p\ge\lfloor c/2\rfloor$ the truncated hypothesis reads $e(G_c)>h(c+1,0)=\binom{c+1}{2}$, which no graph on $c$ vertices satisfies, exactly as with the paper's integer value. "$G_c-S$ is a clique" means any two distinct vertices outside $S$ are adjacent.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 10, Lemma 2.11

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
open Finset SimpleGraph

namespace CircStability.Main

theorem lemma_2_11 {V : Type*} [Fintype V] [DecidableEq V] (c p : ℕ) (hV : Fintype.card V = c)
    (Gc : SimpleGraph V) [DecidableRel Gc.Adj] (hδ : ∀ v, 2 ≤ Gc.degree v)
    (hcl : IsKClosed (c + 1) Gc) (hH : ¬ HamConnected Gc)
    (hE : hNum (c + 1) (c / 2 - p) < #Gc.edgeFinset) :
    (∃ s : ℕ, 2 ≤ s ∧ s ≤ c / 2 - p - 1 ∧
      ∃ S : Finset V, #S = s - 1 ∧ (∀ v ∈ S, Gc.degree v ≤ s) ∧
        ∀ u v, u ∉ S → v ∉ S → u ≠ v → Gc.Adj u v) ∨
    (∃ t : ℕ, c / 2 - p + 1 ≤ t ∧ t ≤ c / 2 ∧
      ∃ T : Finset V, #T = t - 1 ∧ ∀ v ∈ T, Gc.degree v ≤ t) := by sorry

end CircStability.Main
