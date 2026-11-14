-- Prove2me | Theorems.Thm_DvorakNorin2018_tame_cloud_normalization
-- name    : DvorakNorin2018.tame_cloud_normalization
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T17:36:51.375232+00:00
-- url     : https://prove2.me/theorems/1d0efc4c-3909-4089-a2d7-f83b99a4e8c9
-- title:
--   Lemma 6: every bounded-congestion cloud admits tame normalization
-- statement:
--   Let $G$ be a finite undirected graph, let $W$ be a sink set, and let $\alpha,s>0$. If a $W$-cloud has congestion at most $\alpha$ and total supply exactly $s$, then there exists an $\alpha$-tame $W$-cloud with the same total supply. A tame cloud has no incoming flow at hungry vertices, at most one hungry predecessor at each saturated vertex, and, when $\alpha\le1$, has zero edge flow with active vertex set exactly $W$. This is the complete statement of Lemma 6, with source terminology specified by the imported definitions.
-- source:
--   Dvorak–Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Section 2.2, definitions preceding Lemma 6 and its proof (PDF pp. 5–6).

import Definitions.Def_DvorakNorin2018_CloudNormalization
set_option autoImplicit false
open scoped Classical BigOperators
open StableMSR.Recovery.TameCloud

namespace DvorakNorin2018
theorem tame_cloud_normalization {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ) (hα : 0 < α) (hs : 0 < s)
    (p : Data V) (hp : Cloud G W α p) (ht : total p = s) :
    ∃ q : Data V, Cloud G W α q ∧ Tame W α q ∧ total q = s := by sorry
end DvorakNorin2018
