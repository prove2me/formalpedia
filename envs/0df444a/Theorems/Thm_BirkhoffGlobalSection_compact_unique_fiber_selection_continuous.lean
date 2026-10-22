-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_compact_unique_fiber_selection_continuous
-- name    : BirkhoffGlobalSection.compact_unique_fiber_selection_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:41:55.387134+00:00
-- url     : https://prove2.me/theorems/d4865c25-2ae7-4582-8c07-6ef3a3ca270c
-- title:
--   A unique section of a compact relation is continuous
-- statement:
--   A compact relation between unit directions and real radii with exactly one radius over every direction defines a continuous radius function. Compactness supplies closedness of the graph and a continuous inverse to the projection onto directions.
-- source:
--   Standard compact-to-Hausdorff inverse theorem and polar-coordinate topology.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem compact_unique_fiber_selection_continuous
    (G : Set ({x : Phase // x ∈ unitThreeSphere} × ℝ))
    (hcompact : IsCompact G)
    (hunique : ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∃! r : ℝ, (x, r) ∈ G) :
    Continuous (fun x : {x : Phase // x ∈ unitThreeSphere} =>
      Classical.choose (hunique x).exists) := by sorry

end BirkhoffGlobalSection
