-- Prove2me | Theorems.Thm_CircStability_Main_lemma_2_8
-- name    : CircStability.Main.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:25.169847+00:00
-- url     : https://prove2.me/theorems/8feea25c-8042-4603-8624-c480efbfeb35
-- title:
--   Lemma 2.8 — for a locally maximal C of length c ≤ n−1 in a 2-connected G, the closure Ḡ[C] is not Hamiltonian-connected
-- statement:
--   Let $G$ be a 2-connected graph on $n$ vertices and $C$ a locally maximal cycle of $G$ of length $c\le n-1$. Let $\overline G$ be the $C$-closure of $G$. Then
--
--   $$
--   \overline G[C] \text{ is not Hamiltonian-connected.}
--   $$
--
--   Together with Lemma 2.11 this produces the low-degree vertices from which the structure of $\overline G[C]$ is recovered in §4.
--
--   **Formalization Note.** $\overline G[C]$ is the subgraph of $\overline G$ induced on $V(C)$, a graph on the $c$ vertices of $C$. Hamiltonian-connected quantifies over distinct pairs of vertices.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 9, Lemma 2.8

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
open Finset SimpleGraph

namespace CircStability.Main

theorem lemma_2_8 (n c : ℕ) (G : SimpleGraph (Fin n)) (hG : TwoConnected G)
    {u : Fin n} (C : G.Walk u u) (hC : IsLocallyMaximal G C) (hlen : C.length = c)
    (hcn : c ≤ n - 1) :
    ¬ HamConnected ((cClosure G C.support.toFinset).induce
      ((C.support.toFinset : Finset (Fin n)) : Set (Fin n))) := by sorry

end CircStability.Main
