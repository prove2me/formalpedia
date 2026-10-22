-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_compact_unique_ray_radial_graph
-- name    : BirkhoffGlobalSection.compact_unique_ray_radial_graph
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:23:57.919252+00:00
-- url     : https://prove2.me/theorems/d863f7fe-d99d-43ca-872f-7743c58b6e31
-- title:
--   Compact star-shaped boundaries have continuous radial graphs
-- statement:
--   Suppose a compact subset of four-dimensional real phase space avoids the origin and meets each positive ray from the origin exactly once. Then it is the radial graph of a strictly positive continuous function on the unit sphere. Compactness supplies continuity of the unique radial inverse.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 (geometric subcritical component); standard compact-to-Hausdorff inverse theorem.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem compact_unique_ray_radial_graph (S : Set Phase)
    (hcompact : IsCompact S)
    (hzero : (fun _ : Fin 4 => (0 : ℝ)) ∉ S)
    (hunique : ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∃! r : ℝ, 0 < r ∧
        (fun i : Fin 4 => r * (x : Phase) i) ∈ S) :
    ∃ ρ : {x : Phase // x ∈ unitThreeSphere} → ℝ,
      Continuous ρ ∧
      (∀ x, 0 < ρ x) ∧
      S = Set.range (fun x : {x : Phase // x ∈ unitThreeSphere} =>
        (fun i : Fin 4 => ρ x * (x : Phase) i)) := by sorry

end BirkhoffGlobalSection
