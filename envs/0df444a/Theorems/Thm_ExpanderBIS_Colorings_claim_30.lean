-- Prove2me | Theorems.Thm_ExpanderBIS_Colorings_claim_30
-- name    : ExpanderBIS.Colorings.claim_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:15.628996+00:00
-- url     : https://prove2.me/theorems/88bf0439-2590-4dea-b12b-f116c11b150b
-- title:
--   Claim 30 — a sparse set S has |S| ≤ 12q (log Δ/Δ) m
-- statement:
--   Let $q \ge 3$, $\Delta \ge 3$, and let $G$ be a $\Delta$-regular bipartite graph with sides of size $m$ that is a $\bigl(\frac{4\log\Delta}{\Delta}, \frac{\Delta}{4\log\Delta} - \frac12\bigr)$-expander. If $S \subseteq V$ is sparse, i.e. every $G^3$-connected component of $S$ is little, then
--   $$|S| \le 12q\,\frac{\log\Delta}{\Delta}\, m.$$
--
--   Claim 30 bounds the size of the sets that the polymer models count, and so the number of colorings that Lemma 29's approximant counts beyond those with a little disagreement set.
--
--   **Formalization Note.** $\Delta \ge 3$ is the paper's standing convention (§1.3, p. 5).
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 28, Claim 30 (sparse: p. 28)

import Mathlib
import Definitions.Def_ExpanderBIS_Colorings_Setting

open Classical Finset

namespace ExpanderBIS.Colorings

theorem claim_30 {m Δ q : ℕ} (hq : 3 ≤ q) (hΔ : 3 ≤ Δ) (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m))
    (hG : G ∈ ExpanderBIS.RandomHardCore.Gbip m Δ) (hexp : ExpanderBIS.RandomHardCore.IsStdExpander G Δ) (S : Finset (ExpanderBIS.RandomHardCore.Vertex m))
    (hS : IsSparse G q Δ S) :
    (S.card : ℝ) ≤ 12 * q * (Real.log Δ / Δ) * m := by sorry

end ExpanderBIS.Colorings
