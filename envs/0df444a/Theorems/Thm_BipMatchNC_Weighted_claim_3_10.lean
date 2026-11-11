-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_claim_3_10
-- name    : BipMatchNC.Weighted.claim_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:15:57.206196+00:00
-- url     : https://prove2.me/theorems/b1842836-e234-413f-9867-150b75b470cf
-- title:
--   Claim 3.10: every left-saturating matching of the blow-up graph G^{r,δ} has weight at most rw* + 2n³δW
-- statement:
--   Let $G$ be a balanced bipartite graph on $[n]+[n]$ with weights $w:E\to\mathbb N$ that has a perfect matching; let $w^*$ be the maximum weight of a perfect matching and $W$ the maximum edge weight. Let $\delta\ge n$, $r>4n^3\delta W$ and $D=n(r-\delta)$, and let $G^{r,\delta}$ be the blow-up graph with induced weights $\hat w$. Then every left-saturating matching $\hat M$ of $G^{r,\delta}$ satisfies
--   $$\hat w(\hat M)\le r\,w^*+2n^3\delta W.$$
--
--   Since the degree of $\det M(G,w)[S]$ is at most the maximum weight of a perfect matching of $G^{r,\delta}[S]$, this bounds $\deg\mathcal D_w(t)$ from above by $2rw^*+4n^3\delta W$ (inequality (3.7)).
--
--   Differences from the source:
--   - encoding: the maximum weight of any left-saturating matching in G^{r,δ} is bounded by B → every f with IsLeftSaturatingOn (blowUpAdj G r D) f has matchingWeight (blowUpWeight w r D) f ≤ B; reason: a maximum is bounded iff every element is
--   - encoding: G^{r,δ} with vertices u_{i,p}, v_{j,q}, a_{i,q} → left vertices Fin n × Fin D, right vertices Fin (n * n) × Fin r (the column indices of M(G), see the BlowUp definition); reason: indexing convention; same graph and weights
--   - encoding: w* is the weight of a maximum weight perfect matching M* of G (p. 14), so G has one → hypothesis G.HasPM; w* is G.maxPMWeight w; reason: w* is only defined when a perfect matching exists
--   - encoding: §3.3 parameters δ ≥ n, r > 4n³δW, D = n(r − δ) → n ≤ δ, 4 * n ^ 3 * δ * W < r, D written as n * (r - δ) in ℕ; reason: standing assumptions of §3.3; if r ≤ δ (possible only when W = 0) the page's D is not a dimension and ℕ-subtraction gives D = 0, where the claim is trivial; γ and α do not occur in the claim
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 16 (PDF 17), Claim 3.10

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Bipartite
import Definitions.Def_BipMatchNC_Weighted_Graph
import Definitions.Def_BipMatchNC_Weighted_BlowUp

namespace BipMatchNC.Weighted

theorem claim_3_10 (n r δ : ℕ) (G : BipGraph n) (w : Fin n → Fin n → ℕ) (hPM : G.HasPM)
    (hδ : n ≤ δ) (hr : 4 * n ^ 3 * δ * G.maxEdgeWeight w < r)
    (f : Fin n × Fin (n * (r - δ)) → Fin (n * n) × Fin r)
    (hf : IsLeftSaturatingOn (blowUpAdj G r (n * (r - δ))) f) :
    matchingWeight (blowUpWeight w r (n * (r - δ))) f ≤
      r * G.maxPMWeight w + 2 * n ^ 3 * δ * G.maxEdgeWeight w := by sorry

end BipMatchNC.Weighted
