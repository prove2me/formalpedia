-- Prove2me | Theorems.Thm_Esgk_distinct_distances_one_fifth_excess
-- name    : Esgk.distinct_distances_one_fifth_excess
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-12T19:34:17.409456+00:00
-- url     : https://prove2.me/theorems/23105be7-912c-467a-8f19-b74f9385cc6e
-- title:
--   An additive n^(1/5) improvement for distinct distances
-- statement:
--   There exist an absolute real constant $c>0$ and a natural-number threshold $N$ such that, for every $n\ge N$ and every injective configuration of $n$ points in the Euclidean plane with no three collinear and no four cocircular, the number $D(P)$ of distinct distances between different points satisfies
--
--   $$D(P)\ge \frac n3+c n^{1/5}.$$
--
--   Here $P$ is the image of the configuration and $D(P)$ counts the distinct values of `dist x y` for different $x,y\in P$. The same $c$ and $N$ must work for all such configurations. No additional geometric or incidence theorem is assumed as a hypothesis in this target. Status: CONJECTURED.
-- source:
--   Self-contained formal statement prepared for this mission.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Esgk_Foundation

open EuclideanGeometry Filter

namespace Esgk

/-- Seek the one-fifth additive-excess improvement under full planar general position.
This is CONJECTURED. -/
theorem distinct_distances_one_fifth_excess :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          (n : ℝ) / 3 + c * Real.rpow (n : ℝ) (1 / 5 : ℝ) ≤
            (distinctDistances (Config.toFinset p) : ℝ) := by
  sorry

end Esgk
