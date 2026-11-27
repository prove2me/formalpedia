-- Prove2me | Theorems.Thm_Esgk_general_position_five_exact
-- name    : Esgk.general_position_five_exact
-- status  : Proved
-- author  : @DavidDenisov
-- created : 2026-11-27T02:09:47.109092+00:00
-- url     : https://prove2.me/theorems/03079369-9e18-54f3-8a68-e559b3b22255
-- title:
--   Five planar points in general position have an exact minimum of three distances
-- statement:
--   Among five points in the Euclidean plane with no three collinear and no four concyclic, the minimum number of distinct distances between unordered pairs is exactly three. The lower bound holds for every such five-point configuration, and a configuration attaining it exists. This is the five-point exact case of the alternative target recorded in the planar distinct-distance mission.
-- source:
--   Prove2Me, Superlinear or exact bounds for planar distinct distances, exact-bounds alternative (n = 5); https://prove2.me/missions/5e2ef798-f443-4343-8d92-e597e053512f. Related open problem: Erdős Problem 98.

import Definitions.Def_Esgk_Foundation

open EuclideanGeometry

namespace Esgk

theorem general_position_five_exact :
    (∀ p : Config 5, Function.Injective p → InGeneralPosition p.toFinset →
      3 ≤ distinctDistances p.toFinset) ∧
      ∃ p : Config 5, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
        distinctDistances p.toFinset = 3 := by sorry

end Esgk
