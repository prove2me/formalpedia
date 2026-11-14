-- Prove2me | Theorems.Thm_DvorakNorin2018_minimum_cloud_rerouting
-- name    : DvorakNorin2018.minimum_cloud_rerouting
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T17:37:00.392363+00:00
-- url     : https://prove2.me/theorems/bcbc75a7-c522-4097-aedc-605f697a3a87
-- title:
--   Lemma 6: minimum clouds satisfy the finite rerouting properties
-- statement:
--   Let $\alpha>1$ and fix the total supply $s$. Every lexicographic minimum cloud has no positive flow into a hungry vertex, and every saturated vertex has at most one hungry predecessor carrying positive flow into it. These are precisely properties (i) and (ii) of tameness. This is the finite rerouting part of Lemma 6. The source derives these properties by cancelling directed cycles, shortening a positive-flow path into a hungry vertex, and shifting supply between two hungry predecessors. This theorem does not assume either structural property as a hypothesis.
-- source:
--   Dvorak–Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Section 2.2, definitions preceding Lemma 6 and its proof (PDF pp. 5–6).

import Definitions.Def_DvorakNorin2018_CloudNormalization
set_option autoImplicit false
open scoped Classical BigOperators
open StableMSR.Recovery.TameCloud

namespace DvorakNorin2018
theorem minimum_cloud_rerouting {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ) (hα : 1 < α)
    (p : Data V) (hp : IsLexMinimum G W α s p) : ReroutingConclusion W p := by sorry
end DvorakNorin2018
