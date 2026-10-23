-- Prove2me | Theorems.Thm_CircletTSP_Facet_proposition_4_5
-- name    : CircletTSP.Facet.proposition_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:16.823986+00:00
-- url     : https://prove2.me/theorems/b0195b7d-89eb-4c8b-9fa7-900f4599846b
-- title:
--   Proposition 4.5, p. 17 — the second contraction saves an even amount ≥ 2 (inequality (6)), and another edge drops when it is 2
-- statement:
--   Let $n$ be a positive multiple of $4$, $d=n/2$, labels $1,\dots,n$. Let $j\ne k$ be labels outside $\{1,2,d+1,d+2\}$, and consider contracting $\{j,d+2\},\{d+2,2\},\{2,1\},\{1,d+1\},\{d+1,k\}$ into $\{j',k'\}$. Write
--   $$\Delta=c_{j,d+2}+c_{d+2,2}+c_{2,1}+c_{1,d+1}+c_{d+1,k}-c'_{j',k'} .$$
--   Then:
--
--   1. $\Delta\ge 2$ (inequality (6)) and $\Delta$ is even;
--   2. if $\Delta=2$, then every Hamiltonian cycle on $K_n$ containing these five edges also contains an edge $\{s,t\}$ with $s,t\notin\{1,2,d+1,d+2\}$ and $c'_{s',t'}=c_{s,t}-2$.
--
--   In either case the contracted Hamiltonian cycle (structure A at $u=1$) is at least $4$ cheaper than the original.
--
--   **Formalization Note** Costs are integers. The cycle is an ordering `π : Equiv.Perm (Fin n)`; "contains the edge $\{a,b\}$" refers to the vertices with labels $a,b$ (vertex `v` has label $v+1$). The concluding sentence "In either case …" is the separate item `contraction_step`.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 17, Proposition 4.5, inequality (6)

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Proposition 4.5 (p. 17): contracting `{j, d + 2}, {d + 2, 2}, {2, 1}, {1, d + 1}, {d + 1, k}`
into `{j', k'}` lowers the cost of these edges by an even amount that is at least `2` (inequality
(6)); and if it is exactly `2`, then every Hamiltonian cycle containing these five edges has
another edge `{s, t}` with `s, t ∉ {1, 2, d + 1, d + 2}` whose cost drops by `2`
(1-based labels, `d = n / 2`). -/
theorem proposition_4_5 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hjk : j ≠ k) :
    2 ≤ labCost n j (n / 2 + 2) + labCost n (n / 2 + 2) 2 + labCost n 2 1 +
        labCost n 1 (n / 2 + 1) + labCost n (n / 2 + 1) k - conCost n (relabel n j) (relabel n k) ∧
      Even (labCost n j (n / 2 + 2) + labCost n (n / 2 + 2) 2 + labCost n 2 1 +
        labCost n 1 (n / 2 + 1) + labCost n (n / 2 + 1) k -
          conCost n (relabel n j) (relabel n k)) ∧
      ∀ π : Equiv.Perm (Fin n), ChainTwo π j k →
        labCost n j (n / 2 + 2) + labCost n (n / 2 + 2) 2 + labCost n 2 1 +
            labCost n 1 (n / 2 + 1) + labCost n (n / 2 + 1) k -
              conCost n (relabel n j) (relabel n k) = 2 →
          ∃ s ∈ keptLabels n, ∃ t ∈ keptLabels n, HasEdge π s t ∧
            conCost n (relabel n s) (relabel n t) = labCost n s t - 2 := by sorry

end CircletTSP.Facet
