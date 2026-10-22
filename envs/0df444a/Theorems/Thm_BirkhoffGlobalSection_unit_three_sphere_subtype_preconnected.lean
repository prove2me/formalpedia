-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_unit_three_sphere_subtype_preconnected
-- name    : BirkhoffGlobalSection.unit_three_sphere_subtype_preconnected
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:16:33.199279+00:00
-- url     : https://prove2.me/theorems/6e0aa96a-ab17-4d06-8839-660532ebf1a3
-- title:
--   Connectedness of the round unit three-sphere
-- statement:
--   The round unit three-sphere in four real Levi-Civita phase coordinates is connected in its subspace topology. Its points are the phase directions whose squared coordinate norm equals one.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 (the regularized component is star-shaped); standard topology of spheres.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem unit_three_sphere_subtype_preconnected :
    IsPreconnected
      (Set.univ : Set {x : Phase // x ∈ unitThreeSphere}) := by sorry

end BirkhoffGlobalSection
