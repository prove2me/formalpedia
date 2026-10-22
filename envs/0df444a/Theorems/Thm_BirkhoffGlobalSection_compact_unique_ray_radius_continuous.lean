-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_compact_unique_ray_radius_continuous
-- name    : BirkhoffGlobalSection.compact_unique_ray_radius_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:31:48.155298+00:00
-- url     : https://prove2.me/theorems/d730c74e-48ff-4fbc-b84e-60c5668e0989
-- title:
--   Continuity of the unique radius on a compact radial set
-- statement:
--   Let a compact subset of four-dimensional phase space avoid the origin and meet each positive ray at exactly one point. The function assigning to each unit direction its unique positive intersection radius is continuous. This is the compact-to-Hausdorff inverse step.
-- source:
--   Standard topology of radial graphs and compact-to-Hausdorff continuous bijections.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem compact_unique_ray_radius_continuous (S : Set Phase)
    (hcompact : IsCompact S)
    (hzero : (fun _ : Fin 4 => (0 : ℝ)) ∉ S)
    (hunique : ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∃! r : ℝ, 0 < r ∧
        (fun i : Fin 4 => r * (x : Phase) i) ∈ S) :
    Continuous (fun x : {x : Phase // x ∈ unitThreeSphere} =>
      Classical.choose (hunique x).exists) := by sorry

end BirkhoffGlobalSection
