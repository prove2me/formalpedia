-- Prove2me | Theorems.Thm_Chou_constructible_subgroup_and_quotient
-- name    : Chou.constructible_subgroup_and_quotient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:53:25.255462+00:00
-- url     : https://prove2.me/theorems/a4c0693b-c186-451f-a5a1-a92f6dbb9694
-- title:
--   Proposition 2.1: constructible groups are closed under subgroups and quotients
-- statement:
--   If $G$ is constructible (built from finite and abelian groups by extensions and directed
--   unions), then every subgroup of $G$ is constructible, and for every normal subgroup $N$ of $G$ the
--   quotient $G/N$ is constructible.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Proposition 2.1, p. 397

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- Proposition 2.1: the constructible groups are closed under processes (I) and (II), that is,
under passing to subgroups and to factor groups. -/
theorem constructible_subgroup_and_quotient {G : Type*} [Group G] (h : Constructible G) :
    (∀ H : Subgroup G, Constructible H) ∧
      (∀ (N : Subgroup G) [N.Normal], Constructible (G ⧸ N)) := by
  sorry

end Chou
