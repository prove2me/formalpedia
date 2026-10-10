-- Prove2me | Theorems.Thm_CircStability_Main_lemma_4_4
-- name    : CircStability.Main.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:55.50208+00:00
-- url     : https://prove2.me/theorems/54417969-69b2-45a8-9a73-81e2820b2ca1
-- title:
--   Lemma 4.4 — δ ≥ k, C locally maximal of length c ≤ n−1 and ω(G[C]) ≥ c−k+1 force G ∈ {W_{n,k,c}, Z_{n,k,c}}
-- statement:
--   Let $k\ge2$, let $G$ be a 2-connected graph on $n$ vertices with minimum degree $\delta(G)\ge k$, and let $C$ be a locally maximal cycle of $G$ of length $c\le n-1$. If the clique number of $G[C]$ is at least $c-k+1$, then
--
--   $$
--   G\cong W_{n,k,c}\quad\text{or}\quad G\cong Z_{n,k,c}.
--   $$
--
--   This is the structural core of §4: a large clique on a locally maximal cycle determines the whole graph.
--
--   **Formalization Note.** "$G\in\{W_{n,k,c},Z_{n,k,c}\}$" is read as isomorphism. The alternative $Z_{n,k,c}$ carries the divisibility $(k-1)\mid n-(c-k+1)$, without which $Z_{n,k,c}$ does not exist. The hypothesis $k\ge2$ is the series' standing restriction: the page's main theorems are false at $k=1$, and $Z_{n,k,c}$ divides by $k-1$. The proof on p. 26 invokes "$c\ge2k$ by Dirac's theorem", which the page justifies for a longest cycle while the lemma assumes only a locally maximal one; the statement here is the literal one, without an added $c\ge2k$.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 17, Lemma 4.4 (restated p. 23; proof pp. 23–29)

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
open Finset SimpleGraph

namespace CircStability.Main

theorem lemma_4_4 (n k c : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) (hδ : ∀ v, k ≤ G.degree v) {u : Fin n} (C : G.Walk u u)
    (hC : IsLocallyMaximal G C) (hlen : C.length = c) (hcn : c ≤ n - 1)
    (hω : c - k + 1 ≤
      (G.induce ((C.support.toFinset : Finset (Fin n)) : Set (Fin n))).cliqueNum) :
    Nonempty (G ≃g wGraph n k c) ∨
      ((k - 1) ∣ (n - (c - k + 1)) ∧ Nonempty (G ≃g zGraph n k c)) := by sorry

end CircStability.Main
