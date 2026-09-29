-- Prove2me | Theorems.Thm_Esgk_distinct_distances_one_fourth_excess
-- name    : Esgk.distinct_distances_one_fourth_excess
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-14T06:08:07.492324+00:00
-- url     : https://prove2.me/theorems/89271c6d-2249-4ee4-b34a-da9858088e8d
-- title:
--   An additive n^(1/4) improvement for distinct distances
-- statement:
--   There exist an absolute real constant $c>0$ and a natural-number threshold $N$ such that, for every $n\ge N$ and every injective configuration of $n$ points in the Euclidean plane with no three collinear points and no four cocircular points, the number $D(P)$ of distinct distances between different points satisfies
--
--   $$D(P)\ge \frac n3+c n^{1/4}.$$
--
--   Here $P$ is the image of the configuration and $D(P)$ counts the distinct values of `dist x y` for different $x,y\in P$. The same $c$ and $N$ work for every such configuration. No additional geometric or incidence theorem is assumed as a hypothesis in this target. The cited project source proves the statement at pen-and-paper level; the Lean target remains open.
-- source:
--   Adam McKenna, Atomic proof of the ESGK n^(1/4) additive bound, revision 2026-09-14, Theorem 1.1 and equations (16.7)--(16.9): https://github.com/flound1129/esgk-on3/blob/9e63c1648017becfc717d7e0e4f2877925ace28d/docs/results/esgk-n14-atomic-proof-2026-09-13.md

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
