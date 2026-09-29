-- Prove2me | Theorems.Thm_CannonFloydParry_isReduced_represents_unique
-- name    : CannonFloydParry.isReduced_represents_unique
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:10:48.081945+00:00
-- url     : https://prove2.me/theorems/171bf1d0-72c1-4154-96c8-83a463c8ef56
-- title:
--   A reduced tree diagram is unique
-- statement:
--   If two reduced tree diagrams both represent the same element $f$ of $F$, they are
--   equal — the same domain tree and the same range tree.
--
--   With the previous statement this gives the canonical bijection between $F$ and the set of
--   reduced tree diagrams.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 221 (uniqueness of the reduced diagram)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem isReduced_represents_unique {f : UI ≃o UI} {d₁ d₂ : TreeDiagram}
    (h₁ : IsReduced d₁) (hr₁ : Represents d₁ f)
    (h₂ : IsReduced d₂) (hr₂ : Represents d₂ f) :
    d₁ = d₂ := by
  sorry

end CannonFloydParry
