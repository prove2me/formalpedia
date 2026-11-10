-- Prove2me | Theorems.Thm_BipDijoin_lemma_6_6
-- name    : BipDijoin.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:23.647076+00:00
-- url     : https://prove2.me/theorems/d6180cf7-f519-4d9c-baa6-ed04b034323d
-- title:
--   Lemma 6.6 — $\Phi_\eta=\max_{X\subseteq L}\{|X|-\eta|N_G(X)|\}$
-- statement:
--   Let $G=(L\cup R,E)$ be a bipartite multigraph, $\eta\in[0,1]$, and $x$ any balanced server flow on $G$ with loads $\alpha$. Then
--   $$\Phi_\eta=\sum_{r\in R}\big(\alpha(r)-\eta\big)_+=\max_{X\subseteq L}\big\{|X|-\eta\,|N_G(X)|\big\}.$$
--
--   The combinatorial form shows how much potential can be lost when a perfectly matched set is deleted (Lemma 6.7).
--
--   **Formalization Note** If some left vertex has no edge, no server flow exists and the statement is vacuous, as in the paper.
--
--   Differences from the source:
--   - reading: Φ_η(G), defined through the load vector of a balanced server flow, unique by [BHR19] → Φ_η of every balanced server flow x on G; reason: the uniqueness is cited; a statement for every balanced flow gives the source's statement whatever the flow
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Lemma 6.6, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsServerFlow

set_option autoImplicit false

namespace BipDijoin

/-- **Lemma 6.6** (Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6),
p.30 = PDF p.32). "For every bipartite graph G = (L ∪ R, E), Φ_η(G) = max_{X⊆L} {|X| − η|N_G(X)|}."

Let `G` be a well-formed bipartite multigraph, `η ∈ [0, 1]` (fixed in §6.3.2) and `x` any balanced
server flow on `G`. Then `Φ_η = Σ_{r ∈ R} (α(r) − η)₊` is the largest value of `|X| − η|N_G(X)|`
over the sets `X ⊆ L`.

**Formalization Note.** The paper's `Φ_η(G)` uses the load vector of a balanced server flow, which
is unique [BHR19]; the statement holds for every balanced server flow, so that uniqueness is not
needed. If some left vertex has no edge, no server flow exists and the statement is vacuous. -/
theorem lemma_6_6 (G : BipGraph) (hG : G.WF) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x : ℕ → ℝ)
    (hx : G.IsBalancedServerFlow x) :
    IsGreatest ((fun X : Finset ℕ => (X.card : ℝ) - η * (G.nbr X).card) '' {X | X ⊆ G.left})
      (G.Phi η x) := by sorry

end BipDijoin
