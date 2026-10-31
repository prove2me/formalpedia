-- Prove2me | Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_39
-- name    : ConcreteSheaves.Quasitopos.proposition_39
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:37.245671+00:00
-- url     : https://prove2.me/theorems/170329f9-0c0b-4e49-b7f9-1fd6a077aea2
-- title:
--   Proposition 39 — all small limits are computed pointwise
-- statement:
--   Let $(D,K,T)$ be a small concrete site, where $K$ is its coverage and $T$ is a terminal domain. Write $\mathrm{DSpace}(D)$ for its category of concrete sheaves and natural transformations. Then
--
--   $$
--   \mathrm{DSpace}(D)\text{ has all small limits, and its inclusion into presheaves preserves them.}
--   $$
--
--   Since presheaf limits are computed at each domain, the preservation assertion expresses the paper's pointwise computation. This result supplies the finite limits used by the classifier and slice constructions.
--
--   **Formalization Note** The site and presheaf values lie in universe $u$, covering families are presieves, and the chosen terminal object is explicit data. The inclusion is the full-subcategory functor, so maps of $D$ spaces are natural transformations.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, p. 30, Proposition 39

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits

universe u
variable {D : Type u} [SmallCategory D]

/-- Baez–Hoffnung, Proposition 39, p. 30. -/
theorem proposition_39 (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    HasLimits (DSpace K T) ∧ PreservesLimits (IsDSpace K T).ι := by sorry

end ConcreteSheaves.Quasitopos
