-- Prove2me | Theorems.Thm_CircStability_Main_lemma_2_10
-- name    : CircStability.Main.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:05.632056+00:00
-- url     : https://prove2.me/theorems/df99b519-4a40-4f4c-bc38-af3bc3c1762f
-- title:
--   Lemma 2.10 — a non-Hamiltonian-connected graph with δ ≥ 2 has s − 1 vertices of degree ≤ s, 2 ≤ s ≤ ⌊n/2⌋
-- statement:
--   Let $G$ be a graph on $n$ vertices with minimum degree at least $2$ that is not Hamiltonian-connected. Then there is an integer $s$ with
--
--   $$
--   2\le s\le\lfloor n/2\rfloor
--   $$
--
--   and a set of $s-1$ vertices of $G$, each of degree at most $s$.
--
--   This is the corollary of Chvátal's degree-sequence condition for Hamiltonicity (Theorem 2.9) that drives Lemma 2.11.
--
--   **Formalization Note.** The graph is on an arbitrary finite vertex type of size $n$; Hamiltonian-connected quantifies over distinct pairs.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 10, Lemma 2.10

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
open Finset SimpleGraph

namespace CircStability.Main

theorem lemma_2_10 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hH : ¬ HamConnected G) (hδ : ∀ v, 2 ≤ G.degree v) :
    ∃ s : ℕ, 2 ≤ s ∧ s ≤ Fintype.card V / 2 ∧
      ∃ T : Finset V, #T = s - 1 ∧ ∀ v ∈ T, G.degree v ≤ s := by sorry

end CircStability.Main
