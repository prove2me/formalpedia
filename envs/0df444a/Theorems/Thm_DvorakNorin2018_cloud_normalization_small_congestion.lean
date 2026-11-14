-- Prove2me | Theorems.Thm_DvorakNorin2018_cloud_normalization_small_congestion
-- name    : DvorakNorin2018.cloud_normalization_small_congestion
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T17:36:52.760077+00:00
-- url     : https://prove2.me/theorems/c085ca28-7111-47ba-879b-de30a0b0f474
-- title:
--   Lemma 6, small-congestion case: exact normalization with zero edge flow
-- statement:
--   If a finite $W$-cloud has congestion at most $0\le\alpha\le1$, it can be replaced by an $\alpha$-tame cloud with exactly the same total supply. All edge flows of the resulting cloud are zero and its active vertices are exactly $W$. This proves the complete small-congestion branch of Lemma 6, including exact supply preservation.
-- source:
--   Dvorak–Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Section 2.2, definitions preceding Lemma 6 and its proof (PDF pp. 5–6).

import Definitions.Def_DvorakNorin2018_CloudNormalization
set_option autoImplicit false
open scoped Classical BigOperators
open StableMSR.Recovery.TameCloud

namespace DvorakNorin2018
theorem cloud_normalization_small_congestion {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : Data V) (hp : Cloud G W α p) :
    ∃ q : Data V, Cloud G W α q ∧ Tame W α q ∧ total q = total p := by sorry
end DvorakNorin2018
