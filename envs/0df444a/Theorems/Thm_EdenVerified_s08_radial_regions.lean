-- Prove2me | Theorems.Thm_EdenVerified_s08_radial_regions
-- name    : EdenVerified.s08_radial_regions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:23:27.92628+00:00
-- url     : https://prove2.me/theorems/912137c8-7284-422d-a4ed-b29bdd41ac2d
-- title:
--   Eden Verified: s08 radial regions
-- statement:
--   The nonempty disjoint relatively open regions and their strict invariance.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L281-L292
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L281-L292

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s08_radial_regions (c : ℝ) :
    innerRadialRegion.Nonempty ∧ outerRadialRegion.Nonempty ∧
    Disjoint innerRadialRegion outerRadialRegion ∧
    IsOpen {p : attractor | (p : PhaseSpace) ∈ innerRadialRegion} ∧
    IsOpen {p : attractor | (p : PhaseSpace) ∈ outerRadialRegion} ∧
    (∀ t : ℝ, 0 ≤ t → evolution c t '' innerRadialRegion = innerRadialRegion ∧
      evolution c t '' outerRadialRegion = outerRadialRegion ∧
      evolution c t '' unitRadialLevel = unitRadialLevel) := by sorry
