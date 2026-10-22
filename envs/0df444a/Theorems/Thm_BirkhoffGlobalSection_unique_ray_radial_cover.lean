-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_unique_ray_radial_cover
-- name    : BirkhoffGlobalSection.unique_ray_radial_cover
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:31:50.62696+00:00
-- url     : https://prove2.me/theorems/411ae77a-bc91-45db-b22d-19a5d7bd09ed
-- title:
--   Unique positive ray points cover a set avoiding the origin
-- statement:
--   If a subset of four-dimensional phase space avoids the origin and meets every positive ray exactly once, normalizing each of its points to a unit direction shows that the set equals the range of the selected radial graph.
-- source:
--   Standard topology of radial graphs and compact-to-Hausdorff continuous bijections.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem unique_ray_radial_cover (S : Set Phase)
    (hzero : (fun _ : Fin 4 => (0 : ℝ)) ∉ S)
    (hunique : ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∃! r : ℝ, 0 < r ∧
        (fun i : Fin 4 => r * (x : Phase) i) ∈ S) :
    S = Set.range (fun x : {x : Phase // x ∈ unitThreeSphere} =>
      (fun i : Fin 4 =>
        Classical.choose (hunique x).exists * (x : Phase) i)) := by sorry

end BirkhoffGlobalSection
