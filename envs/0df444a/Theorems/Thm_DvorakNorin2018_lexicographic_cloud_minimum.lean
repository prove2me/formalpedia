-- Prove2me | Theorems.Thm_DvorakNorin2018_lexicographic_cloud_minimum
-- name    : DvorakNorin2018.lexicographic_cloud_minimum
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T17:36:52.614317+00:00
-- url     : https://prove2.me/theorems/2221e927-f35b-428f-9211-59a3ecea3b6e
-- title:
--   Lemma 6: a lexicographically minimum cloud exists
-- statement:
--   Given any feasible $W$-cloud of prescribed total supply $s$ and congestion at most $\alpha$ on a finite graph, there exists a cloud of the same supply and congestion bound that lexicographically minimizes total edge flow and then support size minus saturated-vertex count. The secondary objective is expressed as support size plus unsaturated-vertex count, which differs only by a graph-dependent constant. This proves the extremal selection asserted in the first paragraph of Lemma 6: compactness attains the continuous primary objective, and well-ordering selects the secondary optimum.
-- source:
--   Dvorak–Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Section 2.2, definitions preceding Lemma 6 and its proof (PDF pp. 5–6).

import Definitions.Def_DvorakNorin2018_CloudNormalization
set_option autoImplicit false
open scoped Classical BigOperators
open StableMSR.Recovery.TameCloud

namespace DvorakNorin2018
theorem lexicographic_cloud_minimum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ)
    (p : Data V) (hp : Cloud G W α p) (ht : total p = s) :
    ∃ q : Data V, IsLexMinimum G W α s q := by sorry
end DvorakNorin2018
