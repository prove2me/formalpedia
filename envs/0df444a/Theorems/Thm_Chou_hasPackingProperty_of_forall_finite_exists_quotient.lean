-- Prove2me | Theorems.Thm_Chou_hasPackingProperty_of_forall_finite_exists_quotient
-- name    : Chou.hasPackingProperty_of_forall_finite_exists_quotient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:05:09.09561+00:00
-- url     : https://prove2.me/theorems/5a05ccf0-13fd-44c9-85a5-261af7c2d138
-- title:
--   Lemma 4.6 (a): property (P) from quotients separating finite sets
-- statement:
--   Suppose that for every finite subset $F$ of $G$ there is a normal subgroup $K$ such that $G/K$
--   has property (P) and distinct elements of $F$ have distinct images in $G/K$. Then $G$ has
--   property (P).
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Lemma 4.6 (a), p. 405

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- Lemma 4.6 (a): if for each finite `F ⊆ G` there is a normal subgroup `K` such that `G ⧸ K`
has property (P) and `F` maps injectively into `G ⧸ K`, then `G` has property (P). -/
theorem hasPackingProperty_of_forall_finite_exists_quotient {G : Type*} [Group G]
    (h : ∀ F : Set G, F.Finite → ∃ (K : Subgroup G) (_ : K.Normal),
      HasPackingProperty (G ⧸ K) ∧ Set.InjOn (QuotientGroup.mk : G → G ⧸ K) F) :
    HasPackingProperty G := by
  sorry

end Chou
