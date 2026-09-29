-- Prove2me | Theorems.Thm_Chou_hasPackingProperty_of_directedUnion
-- name    : Chou.hasPackingProperty_of_directedUnion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:03:29.686957+00:00
-- url     : https://prove2.me/theorems/cb488b24-1ada-4090-9b10-5d4f0958349e
-- title:
--   Lemma 4.1 (a): directed unions preserve property (P)
-- statement:
--   If $G$ is the directed union of a family of subgroups each having property (P), then $G$ has
--   property (P).
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Lemma 4.1 (a), p. 403

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- Lemma 4.1 (a): a directed union of subgroups with property (P) has property (P). -/
theorem hasPackingProperty_of_directedUnion {G : Type*} [Group G] {ι : Type*} (H : ι → Subgroup G)
    (hdir : Directed (· ≤ ·) H) (hsup : ⨆ i, H i = ⊤) (h : ∀ i, HasPackingProperty (H i)) :
    HasPackingProperty G := by
  sorry

end Chou
