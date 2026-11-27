-- Prove2me | Theorems.Thm_Esgk_general_position_six_exact
-- name    : Esgk.general_position_six_exact
-- status  : Proved
-- author  : @DavidDenisov
-- created : 2026-11-27T02:42:23.558824+00:00
-- url     : https://prove2.me/theorems/f61531f4-2b78-47bb-b80f-af72ef5d5811
-- title:
--   Six planar points in general position have an exact minimum of four distances
-- statement:
--   Let $h(n)$ be the minimum number of distances determined by $n$ points in the Euclidean plane, with no three collinear and no four cocircular. The six-point exact case of the planar distinct-distance mission is
--   $$h(6)=4.$$
--   Both the universal lower bound and the existence of an attaining configuration are included.
-- source:
--   Prove2Me, Superlinear or exact bounds for planar distinct distances, exact-bounds alternative (n = 5); https://prove2.me/missions/5e2ef798-f443-4343-8d92-e597e053512f. Related open problem: Erdős Problem 98.

import Definitions.Def_Esgk_Foundation

open EuclideanGeometry

namespace Esgk

theorem general_position_six_exact :
    (∀ p : Config 6, Function.Injective p → InGeneralPosition p.toFinset →
      4 ≤ distinctDistances p.toFinset) ∧
      ∃ p : Config 6, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
        distinctDistances p.toFinset = 4 := by sorry

end Esgk
