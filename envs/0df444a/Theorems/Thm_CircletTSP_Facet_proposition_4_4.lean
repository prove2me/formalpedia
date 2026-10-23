-- Prove2me | Theorems.Thm_CircletTSP_Facet_proposition_4_4
-- name    : CircletTSP.Facet.proposition_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:08.28175+00:00
-- url     : https://prove2.me/theorems/445849bb-0209-4a4c-baa0-f32d362f7c54
-- title:
--   Proposition 4.4, p. 17 — the first contraction lowers the cost by at least 4 (inequality (5))
-- statement:
--   Let $n$ be a positive multiple of $4$, $d=n/2$, labels $1,\dots,n$. Let $j\ne k$ be labels outside $\{1,2,d+1,d+2\}$, and consider contracting the five edges $\{j,1\},\{1,2\},\{2,d+2\},\{d+2,d+1\},\{d+1,k\}$ into the single edge $\{j',k'\}$. Then
--   $$c_{j,1}+c_{1,2}+c_{2,d+2}+c_{d+2,d+1}+c_{d+1,k}-c'_{j',k'}\ \ge\ 4. \tag{5}$$
--
--   Together with Proposition 4.3 this shows that a Hamiltonian cycle containing this edge sequence (structure B2 at $u=1$) contracts to a Hamiltonian cycle on $n-4$ vertices that is at least $4$ cheaper.
--
--   **Formalization Note** $c_{i,j}=c_{\ell_{i,j}}$ and $c'_{i,j}$ are integers; the inequality is in $\mathbb Z$. The sentence "Hence the cost of the tour … goes down by at least 4" is the separate item `contraction_step`.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 17, Proposition 4.4, inequality (5)

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Proposition 4.4 (p. 17), inequality (5): contracting `{j, 1}, {1, 2}, {2, d + 2},
{d + 2, d + 1}, {d + 1, k}` into `{j', k'}` lowers the cost by at least `4`
(1-based labels, `d = n / 2`, `j ≠ k` outside `{1, 2, d + 1, d + 2}`). -/
theorem proposition_4_4 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hjk : j ≠ k) :
    labCost n j 1 + labCost n 1 2 + labCost n 2 (n / 2 + 2) + labCost n (n / 2 + 2) (n / 2 + 1) +
        labCost n (n / 2 + 1) k - conCost n (relabel n j) (relabel n k) ≥ 4 := by sorry

end CircletTSP.Facet
