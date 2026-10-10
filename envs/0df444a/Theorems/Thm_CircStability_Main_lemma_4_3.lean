-- Prove2me | Theorems.Thm_CircStability_Main_lemma_4_3
-- name    : CircStability.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:51.584917+00:00
-- url     : https://prove2.me/theorems/cae3f9e3-b585-449b-9510-e72555330a8d
-- title:
--   Lemma 4.3 — S of s−1 low-degree vertices with G[C]−S a clique forces 2 ≤ s ≤ k and ω(G[C]) ≥ c−k+1
-- statement:
--   Let $G$ be a 2-connected graph on $n$ vertices and $C$ a locally maximal cycle of $G$ of length $c\le n-1$. Suppose that
--
--   $$
--   e(G)>\max\big\{f(n,k+1,c),\ f(n,\lfloor c/2\rfloor-1,c)\big\}.
--   $$
--
--   If $G[C]$ contains a set $S$ of $s-1$ vertices, each of degree at most $s$ in $G[C]$, for some integer $2\le s\le\lfloor c/2\rfloor-1$, such that $G[C]-S$ is a clique, then $2\le s\le k$ and the clique number of $G[C]$ is at least $c-k+1$.
--
--   This handles the clique alternative of Lemma 2.11 in the proof of Theorem 4.1, reducing it to Lemma 4.4.
--
--   **Formalization Note.** $k$ is a natural number and enters only through the edge threshold; the lemma assumes no minimum degree. The degree of $v$ in $G[C]$ is the number of neighbours of $v$ on $C$. The clique number is Mathlib's `cliqueNum` of the induced graph on $V(C)$. For $k\ge c$ the natural-number value $c-k+1$ is at most $1$; the conclusion is then still the paper's.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 17, Lemma 4.3 (restated p. 21; proof pp. 21–22)

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
open Finset SimpleGraph

namespace CircStability.Main

theorem lemma_4_3 (n k c : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) {u : Fin n} (C : G.Walk u u) (hC : IsLocallyMaximal G C)
    (hlen : C.length = c) (hcn : c ≤ n - 1)
    (hE : max (fNum n (k + 1) c) (fNum n (c / 2 - 1) c) < #G.edgeFinset)
    (s : ℕ) (hs2 : 2 ≤ s) (hs : s ≤ c / 2 - 1) (S : Finset (Fin n))
    (hSC : S ⊆ C.support.toFinset) (hScard : #S = s - 1)
    (hdeg : ∀ v ∈ S, #(G.neighborFinset v ∩ C.support.toFinset) ≤ s)
    (hcl : ∀ x ∈ C.support.toFinset, ∀ y ∈ C.support.toFinset, x ∉ S → y ∉ S → x ≠ y →
      G.Adj x y) :
    2 ≤ s ∧ s ≤ k ∧
      c - k + 1 ≤ (G.induce ((C.support.toFinset : Finset (Fin n)) : Set (Fin n))).cliqueNum := by sorry

end CircStability.Main
