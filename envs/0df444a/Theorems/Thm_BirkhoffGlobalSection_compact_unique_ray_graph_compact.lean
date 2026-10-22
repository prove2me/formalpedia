-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_compact_unique_ray_graph_compact
-- name    : BirkhoffGlobalSection.compact_unique_ray_graph_compact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:41:57.778338+00:00
-- url     : https://prove2.me/theorems/c29301ee-33fe-46cd-b8c4-6658cd891818
-- title:
--   Compactness of polar graph over a compact set avoiding the origin
-- statement:
--   For a compact set of four-dimensional phase points that omits the origin, all positive radius and unit-direction pairs whose radial product lies in the set form a compact subset of the sphere-times-radius product. This is a polar-coordinate compactness statement.
-- source:
--   Standard compact-to-Hausdorff inverse theorem and polar-coordinate topology.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem compact_unique_ray_graph_compact (S : Set Phase)
    (hcompact : IsCompact S)
    (hzero : (fun _ : Fin 4 => (0 : ℝ)) ∉ S) :
    IsCompact
      {p : {x : Phase // x ∈ unitThreeSphere} × ℝ |
        0 < p.2 ∧
        (fun i : Fin 4 => p.2 * (p.1 : Phase) i) ∈ S} := by sorry

end BirkhoffGlobalSection
