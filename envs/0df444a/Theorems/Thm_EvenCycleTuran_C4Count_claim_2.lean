-- Prove2me | Theorems.Thm_EvenCycleTuran_C4Count_claim_2
-- name    : EvenCycleTuran.C4Count.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:26.509732+00:00
-- url     : https://prove2.me/theorems/031aac3a-1cbc-41ea-92a7-8a2e1b698b74
-- title:
--   Claim 2, p. 13 — for every 2 ≤ l ≤ k some C₂ₗ contains an edge of multiplicity ≥ 2(k−l)k²·C(2k,k)
-- statement:
--   Let $k\ge 2$ and let $G$ be a graph in which any $k$ vertices have at most $k-1$ common neighbours. Run the greedy procedure on the fat $C_4$'s of $G$ (a pair of distinct vertices is fat if it has at least $k$ common neighbours; a $C_4$ is fat if both of its opposite pairs are fat): process the fat $C_4$'s one by one in an arbitrary order, and from each pick one of its four edges that has been picked the smallest number of times so far. Let $m(e)$ be the number of times edge $e$ is picked. Suppose some edge $e$ is picked at least once and
--
--   $$m(e)\ge 2(k-2)k^2\binom{2k}{k}.$$
--
--   Then for every $2\le l\le k$ there is a cycle $C_{2l}$ in $G$ containing an edge $e_l$ with
--
--   $$m(e_l)\ge 2(k-l)k^2\binom{2k}{k}.$$
--
--   At $l=k$ this produces a $C_{2k}$ in $G$, so in a $C_{2k}$-free graph every edge has multiplicity below $2(k-2)k^2\binom{2k}{k}$; this is how the paper bounds the number of fat $C_4$'s.
--
--   **Formalization Note** Two hypotheses differ from the page. (1) The paper's standing graph is $C_{2k}$-free; with that hypothesis Claim 2 would be vacuous, because its conclusion at $l=k$ is a $C_{2k}$. The statement therefore assumes what the proof of the claim uses (p. 13): any $k$ vertices have at most $k-1$ common neighbours ($K_{k,k}$-freeness), which every $C_{2k}$-free graph satisfies. (2) "$e$ is picked at least once" is implied by the multiplicity bound when $k\ge 3$; at $k=2$ the bound is $m(e)\ge 0$, and the proof's base case ("consider any $C_4$ containing $e$") needs $e$ to lie in a fat $C_4$. A greedy run is the structure `GreedyRun`; cycles are subgraphs isomorphic to `cycleGraph (2 * l)`.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 13, Claim 2 (with the greedy procedure and multiplicity of p. 12, §4.1)

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting
open Finset SimpleGraph Filter Topology

namespace EvenCycleTuran.C4Count

/-- Claim 2, p. 13: let `G` be a graph in which any `k` vertices have at most `k − 1` common
neighbours, `R` a run of the greedy procedure on its fat C₄'s, and `e` an edge picked at least
once with m(e) ≥ 2(k−2)k²·C(2k,k). Then for every `2 ≤ l ≤ k` some copy of C₂ₗ in `G` contains
an edge `e'` with m(e') ≥ 2(k−l)k²·C(2k,k). -/
theorem claim_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : 2 ≤ k)
    (hKkk : ∀ S : Finset V, #S = k → #(commonNbrs G S) ≤ k - 1)
    (R : GreedyRun G k) (e : Sym2 V) (he_pos : 0 < R.mult e)
    (he : 2 * (k - 2) * k ^ 2 * (2 * k).choose k ≤ R.mult e)
    (l : ℕ) (hl : 2 ≤ l) (hlk : l ≤ k) :
    ∃ C : G.Subgraph, Nonempty (cycleGraph (2 * l) ≃g C.coe) ∧
      ∃ e' ∈ C.edgeSet, 2 * (k - l) * k ^ 2 * (2 * k).choose k ≤ R.mult e' := by sorry

end EvenCycleTuran.C4Count
