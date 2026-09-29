-- Prove2me | Theorems.Thm_Chou_hasPackingProperty_of_extension
-- name    : Chou.hasPackingProperty_of_extension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:03:59.395443+00:00
-- url     : https://prove2.me/theorems/1cab26cf-e6d4-4f72-a291-eba139882879
-- title:
--   Lemma 4.1 (b): extensions preserve property (P)
-- statement:
--   If $N$ is a normal subgroup of $G$ such that $N$ and $G/N$ have property (P), then $G$ has
--   property (P).
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Lemma 4.1 (b), p. 403 (proof due to S. Yuan)

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- Lemma 4.1 (b): an extension of a group with property (P) by a group with property (P) has
property (P). -/
theorem hasPackingProperty_of_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : HasPackingProperty N) (hQ : HasPackingProperty (G ⧸ N)) : HasPackingProperty G := by
  sorry

end Chou
