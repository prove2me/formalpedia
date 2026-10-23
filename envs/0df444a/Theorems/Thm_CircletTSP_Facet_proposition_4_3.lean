-- Prove2me | Theorems.Thm_CircletTSP_Facet_proposition_4_3
-- name    : CircletTSP.Facet.proposition_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:19.4707+00:00
-- url     : https://prove2.me/theorems/3db3d64c-2e56-4ac9-852d-c0e8d55e269f
-- title:
--   Proposition 4.3, p. 15 — lengths and costs of the surviving edges after contraction
-- statement:
--   Let $n$ be a positive multiple of $4$, $d=n/2$, and use the labels $1,\dots,n$. Let $\{s,t\}$ be an edge with $s,t\notin\{1,2,d+1,d+2\}$, and let $s',t'$ be the labels after contraction. Then
--   $$\ell'_{s',t'}=\begin{cases}\ell_{s,t}, & 3\le s,t\le d \ \text{ or } \ d+3\le s,t\le n,\\ \ell_{s,t}-2, & \text{otherwise.}\end{cases}$$
--   Moreover
--   $$c'_{s',t'}=\begin{cases} c_{s,t}, & (s,t\le d \text{ or } d+3\le s,t) \text{ and } s\not\equiv_2 t,\\ c_{s,t}, & (s\le d,\ d+3\le t \text{ or } t\le d,\ d+3\le s) \text{ and } s\equiv_2 t,\\ c_{s,t}-2, & \text{else.}\end{cases}$$
--   In particular $c'_{s',t'}\le c_{s,t}$: every such edge gets cheaper or keeps its cost after the contraction.
--
--   This controls the cost of all edges of a Hamiltonian cycle that the contraction of §4 leaves in place.
--
--   **Formalization Note** Labels are natural numbers in $\{1,\dots,n\}\setminus\{1,2,d+1,d+2\}$ (`keptLabels n`), with $s\ne t$; lengths and costs are integers, so $\ell_{s,t}-2$ and $c_{s,t}-2$ are not truncated. $0<n$ is added for uniformity (for $n=4$ there are no such labels).
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 15, Proposition 4.3

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Proposition 4.3 (p. 15): for an edge `{s, t}` with `s, t ∉ {1, 2, d + 1, d + 2}`
(1-based labels, `d = n / 2`), the contracted length `ℓ'_{s',t'}` equals `ℓ_{s,t}` when
`s, t` lie in the same group `{3, …, d}` or `{d + 3, …, n}` and `ℓ_{s,t} - 2` otherwise; the
contracted cost `c'_{s',t'}` equals `c_{s,t}` or `c_{s,t} - 2` according to the printed cases;
in particular the cost never increases. -/
theorem proposition_4_3 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (s t : ℕ)
    (hs : s ∈ keptLabels n) (ht : t ∈ keptLabels n) (hst : s ≠ t) :
    conLen n (relabel n s) (relabel n t) =
        (if (3 ≤ s ∧ s ≤ n / 2 ∧ 3 ≤ t ∧ t ≤ n / 2) ∨
            (n / 2 + 3 ≤ s ∧ s ≤ n ∧ n / 2 + 3 ≤ t ∧ t ≤ n)
          then labLen n s t else labLen n s t - 2) ∧
      conCost n (relabel n s) (relabel n t) =
        (if ((s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t)) ∧ s % 2 ≠ t % 2 then
            labCost n s t
          else if ((s ≤ n / 2 ∧ n / 2 + 3 ≤ t) ∨ (t ≤ n / 2 ∧ n / 2 + 3 ≤ s)) ∧
              s % 2 = t % 2 then
            labCost n s t
          else labCost n s t - 2) ∧
      conCost n (relabel n s) (relabel n t) ≤ labCost n s t := by sorry

end CircletTSP.Facet
