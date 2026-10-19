-- Prove2me | Theorems.Thm_Esgk_distinct_distances_one_fourth_excess
-- name    : Esgk.distinct_distances_one_fourth_excess
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-14T06:08:07.492324+00:00
-- url     : https://prove2.me/theorems/89271c6d-2249-4ee4-b34a-da9858088e8d
-- title:
--   An additive n^(1/4) improvement for distinct distances
-- statement:
--   # A fourth-root improvement for planar distinct distances
--
--   For a finite set $P\subset\mathbb R^2$, let
--
--   $$
--   D(P)=\bigl|\{\,\|x-y\|:x,y\in P,\ x\ne y\,\}\bigr|
--   $$
--
--   be the number of distinct positive distances determined by $P$.
--
--   There exist a real constant $c>0$ and an integer $n_0$ such that every finite set $P\subset\mathbb R^2$ with $n=|P|\ge n_0$, no three collinear points, and no four cocircular points satisfies
--
--   $$
--   D(P)\ge \frac n3+c\,n^{1/4}.
--   $$
--
--   The constant and threshold are uniform over all such point sets.
-- source:
--   Proof of a fourth-root additive bound for planar distinct distances (dated 2026-09-13; revision 2026-09-14 UTC; Git revision 9e63c1648017becfc717d7e0e4f2877925ace28d; file SHA-256 8ceaca7bad8c07ce3d56f8bf726a0d273ddc41fd300b777fae1eb6525e087d29); Theorem 1.1 and equations (16.7)--(16.9).

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Esgk_Foundation

open EuclideanGeometry Filter

namespace Esgk

/-- Seek the one-fourth additive-excess improvement under full planar general position.
This statement is proved in the cited paper-level project source; its Lean proof remains open. -/
theorem distinct_distances_one_fourth_excess :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          (n : ℝ) / 3 + c * Real.rpow (n : ℝ) (1 / 4 : ℝ) ≤
            (distinctDistances (Config.toFinset p) : ℝ) := by
  sorry

end Esgk
